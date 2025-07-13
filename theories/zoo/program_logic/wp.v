From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Import
  wp.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  tactics
  notations.
From zoo.language Require Export
  typeclasses.
From zoo.program_logic Require Export
  state_interp.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ : list observation.

#[local] Ltac wp_unseal :=
  rewrite wp.wp_unseal /wp.wp_def;
  select (option thread_id) (fun tid => destruct tid).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma wp_equal_nobranch v1 v2 tid E Φ :
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v1 v2⌝ -∗
      Φ #b
    ) ⊢
    WP v1 == v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit. { iPureIntro. apply base_reducible_equal. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step; iSteps.
  Qed.
  Lemma wp_equal v1 v2 tid E Φ :
    ▷ (
      ( ⌜v1 ≉ v2⌝ -∗
        Φ #false
      ) ∧ (
        ⌜v1 ≈ v2⌝ -∗
        Φ #true
      )
    ) ⊢
    WP v1 == v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_equal_nobranch. iIntros "!>" ([]).
    1: iDestruct "HΦ" as "(_ & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.

  Lemma wp_alloc (tag : Z) n tid E :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      Alloc #tag #n ∷ tid @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header ₊tag ₊n ∗
      meta_token l ⊤ ∗
      l ↦∗ replicate ₊n ()%V
    }}}.
  Proof.
    iIntros "%Htag %Hn %Φ _ HΦ".
    Z_to_nat tag. rewrite Nat2Z.id.
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_alloc _ _ (replicate ₊n ()%V) with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)".
    all: simpl_length.
    iSteps.
  Qed.

  Lemma wp_block_mutable {es tag} vs tid E :
    0 < length es →
    to_vals es = Some vs →
    {{{
      True
    }}}
      Block Mutable tag es ∷ tid @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header tag (length es) ∗
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}}.
  Proof.
    iIntros (Hlen <-%of_to_vals) "%Φ _ HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_alloc with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)".
    all: simpl_length in *.
    iSteps.
  Qed.

  Lemma wp_block_generative {es tag} vs tid E :
    to_vals es = Some vs →
    {{{
      True
    }}}
      Block ImmutableGenerativeStrong tag es ∷ tid @ E
    {{{ bid,
      RET ValBlock (Generative (Some bid)) tag vs;
      True
    }}}.
  Proof.
    iIntros (<-%of_to_vals) "%Φ _ HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma bwp_match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP e ∶ tid @ E {{ Φ }} -∗
    BWP Match #l x_fb e_fb brs ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He >#Hl H".
    iApply bwp_lift_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hinterp Hl") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e_ %σ_ %es -> %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.
  Lemma bwp_match_ctx K `{!LanguageCtx K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP K e ∶ tid @ E {{ Φ }} -∗
    BWP K (Match #l x_fb e_fb brs) ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He Hl H".
    iApply bwp_bind.
    iApply (bwp_match with "Hl"); first done.
    iApply (bwp_bind_inv with "H").
  Qed.
  Lemma wp_match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP e ∷ tid @ E {{ Φ }} -∗
    WP Match #l x_fb e_fb brs ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_match.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp_match with "Hl H"); first done.
  Qed.
  Lemma wp_match_ctx K `{!LanguageCtx K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP K e ∷ tid @ E {{ Φ }} -∗
    WP K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply: bwp_match_ctx.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp_match_ctx with "Hl H"); first done.
  Qed.

  Lemma wp_tag l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #(encode_tag hdr.(header_tag)) -∗
    WP GetTag #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_size l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header_size) -∗
    WP GetSize #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_load l fld dq v tid E :
    {{{
      ▷ (l +ₗ fld) ↦{dq} v
    }}}
      Load #l #fld ∷ tid @ E
    {{{
      RET v;
      (l +ₗ fld) ↦{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_pointsto_valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_store l fld w v tid E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Store #l #fld v ∷ tid @ E
    {{{
      RET ();
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_pointsto_valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wp_xchg l fld w v tid E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Xchg (#l, #fld)%V v ∷ tid @ E
    {{{
      RET w;
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_pointsto_valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wp_cas_nobranch l fld dq v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦{dq} v -∗
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ -∗
      (l +ₗ fld) ↦{dq} v -∗
        ⌜if b then dq = DfracOwn 1 else True⌝ ∗
        (l +ₗ fld) ↦{dq} v ∗
        ( (l +ₗ fld) ↦{dq} (if b then v2 else v) -∗
          Φ #b
        )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hl HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_pointsto_valid with "Hinterp Hl") as %Hlookup.
    iSplit. { iPureIntro. eapply base_reducible_cas. done. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step; first iSteps.
    iDestruct ("HΦ" $! true with "[//] Hl") as "(-> & Hl & HΦ)".
    iMod (state_interp_pointsto_update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.
  Lemma wp_cas_nobranch' l fld v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦ v -∗
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ -∗
      (l +ₗ fld) ↦ (if b then v2 else v) -∗
      Φ #b
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wp_cas_nobranch with "Hl"). iIntros "!> %b".
    destruct b; iSteps.
  Qed.
  Lemma wp_cas l fld dq v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦{dq} v -∗
    ▷ (
      ( ⌜v ≉ v1⌝ -∗
        (l +ₗ fld) ↦{dq} v -∗
        Φ #false
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦{dq} v -∗
          ⌜dq = DfracOwn 1⌝ ∗
          (l +ₗ fld) ↦{dq} v ∗
          ( (l +ₗ fld) ↦ v2 -∗
            Φ #true
          )
      )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wp_cas_nobranch with "Hl"). iIntros "!>" ([] ?) "Hl".
    1: iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.
  Lemma wp_cas' l fld v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦ v -∗
    ▷ (
      ( ⌜v ≉ v1⌝ -∗
        (l +ₗ fld) ↦ v -∗
        Φ #false
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦ v2 -∗
        Φ #true
      )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wp_cas with "Hl").
    iSplit.
    1: iDestruct "HΦ" as "(HΦ & _)".
    2: iDestruct "HΦ" as "(_ & HΦ)".
    all: iSteps.
  Qed.

  Lemma wp_faa l fld (i1 i2 : Z) tid E :
    {{{
      ▷ (l +ₗ fld) ↦ #i1
    }}}
      FAA (#l, #fld)%V #i2 ∷ tid @ E
    {{{
      RET #i1;
      (l +ₗ fld) ↦ #(i1 + i2)
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_pointsto_valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hinterp Hl") as "($ & Hl)";
    iSteps.
  Qed.

  Lemma wp_fork e tid E Φ :
    ▷ (
      ∀ tid v,
      tid ↦ₗ v -∗
      WP e ∶ tid {{ λ _, True }}
    ) -∗
    ▷ Φ ()%V -∗
    WP Fork e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_fork with "Hinterp") as "(Hinterp & Htid)".
    iStep 2. rewrite right_id Nat.add_0_r.
    iApply (wp_bwp with "(H Htid)").
  Qed.

  Lemma wp_get_local tid dq v E :
    {{{
      ▷ tid ↦ₗ{dq} v
    }}}
      GetLocal ∶ tid @ E
    {{{
      RET v;
      tid ↦ₗ{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Htid HΦ".
    iApply bwp_wp.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_thread_pointsto_valid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_set_local tid w v E :
    {{{
      ▷ tid ↦ₗ w
    }}}
      SetLocal v ∶ tid @ E
    {{{
      RET ();
      tid ↦ₗ v
    }}}.
  Proof.
    iIntros "%Φ >Htid HΦ".
    iApply bwp_wp.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp_thread_pointsto_valid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_thread_pointsto_update with "Hinterp Htid") as "($ & Htid)".
    iSteps.
  Qed.

  Lemma wp_proph tid E :
    {{{
      True
    }}}
      Proph ∷ tid @ E
    {{{ prophs pid,
      RET #pid;
      prophet_model' pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply bwp_wp_weak. iIntros.
    iApply bwp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κs Hinterp !>".
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_prophet_new with "Hinterp") as "(%prophs & Hinterp & Hpid)"; first done.
    iSteps.
  Qed.

  Lemma bwp_resolve e pid v prophs tid E Φ :
    Atomic e →
    to_val e = None →
    prophet_model' pid prophs -∗
    BWP e ∶ tid @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet_model' pid prophs' -∗
      Φ res
    }} -∗
    BWP Resolve e #pid v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hatomic %He Hpid H".
    rewrite !bwp_unfold /bwp_pre /= He. simpl in *.
    iIntros "%nt %σ1 %κs Hinterp !>".
    iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
    iSplitR. { iPureIntro. apply reducible_resolve; done. }
    iIntros "!> %κ %κs' %e2 %σ2 %es -> %Hstep H£".
    destruct κ as [| (pid' & (w' & v')) κ _] using rev_ind.
    - exfalso. apply prim_step_resolve_inv in Hstep; last done.
      invert_base_step.
      destruct κ; done.
    - rewrite -assoc.
      apply prim_step_resolve_inv in Hstep; last done.
      invert_base_step. simplify_list_eq.
      iMod ("H" $! _ _ (Val w') σ2 es with "[%] [%] H£") as "H".
      { done. }
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      iMod (state_interp_prophet_resolve with "Hinterp Hpid") as "(%prophs' & -> & $ & Hpid')".
      iApply (bwp_value_mono with "H").
      iSteps.
  Qed.
  Lemma wp_resolve e pid v prophs tid E Φ :
    Atomic e →
    to_val e = None →
    prophet_model' pid prophs -∗
    WP e ∷ tid @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet_model' pid prophs' -∗
      Φ res
    }} -∗
    WP Resolve e #pid v ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_resolve.
    - iIntros "%Hatomic %He Hpid H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp_resolve with "Hpid H"); first done.
  Qed.
End zoo_G.
