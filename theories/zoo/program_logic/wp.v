From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Import
  wp_lifting.
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

Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ : list observation.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma base_reducible_equal v1 v2 σ :
    base_reducible (v1 == v2) σ.
  Proof.
    destruct
      v1 as [[b1 | n1 | l1 | |] | | [] tag1 [| v1 vs1]],
      v2 as [[b2 | n2 | l2 | |] | | [] tag2 [| v2 vs2]].
    all: try (destruct (decide (b1 = b2)); first subst).
    all: try (destruct (decide (n1 = n2)); first subst).
    all: try (destruct (decide (l1 = l2)); first subst).
    all: try (destruct (decide (tag1 = tag2)); first subst).
    all: try (destruct (decide (v1 = v2)); first subst).
    all: try (destruct (decide (vs1 = vs2)); first subst).
    all: auto with zoo.
  Qed.
  Lemma wp_equal v1 v2 E Φ :
    ▷ (
      ( ⌜v1 ≉ v2⌝ -∗
        Φ #false
      ) ∧ (
        ⌜v1 ≈ v2⌝ -∗
        Φ #true
      )
    ) ⊢
    WP v1 == v2 @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit. { iPureIntro. apply base_reducible_equal; done. }
    iIntros "%e2 %σ2 %es %Hstep _ !> !> !>".
    destruct
      v1 as [[b1 | n1 | l1 | |] | | [] tag1 [| v1 vs1]],
      v2 as [[b2 | n2 | l2 | |] | | [] tag2 [| v2 vs2]].
    all: try (destruct (decide (b1 = b2)); first subst).
    all: try (destruct (decide (n1 = n2)); first subst).
    all: try (destruct (decide (l1 = l2)); first subst).
    all: try (destruct (decide (tag1 = tag2)); first subst).
    all: try (destruct (decide (v1 = v2)); first subst).
    all: try (destruct (decide (vs1 = vs2)); first subst).
    all: invert_base_step; simplify; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iSteps
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iSteps
        end
      end.
  Qed.

  Lemma wp_alloc (tag : Z) n E :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      Alloc #tag #n @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header ₊tag ₊n ∗
      meta_token l ⊤ ∗
      l ↦∗ replicate ₊n ()%V
    }}}.
  Proof.
    iIntros "%Htag %Hn %Φ _ HΦ".
    Z_to_nat tag. rewrite Nat2Z.id.
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit; first auto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_alloc _ _ (replicate ₊n ()%V) with "Hσ") as "(Hσ & Hheader & Hmeta & Hl)".
    all: rewrite ?length_replicate //.
    iSteps.
  Qed.

  Lemma wp_block {es tag} vs E :
    0 < length es →
    to_vals es = Some vs →
    {{{
      True
    }}}
      Block Mutable tag es @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header tag (length es) ∗
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}}.
  Proof.
    iIntros (Hlen <-%of_to_vals) "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit; first auto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_alloc with "Hσ") as "(Hσ & Hheader & Hmeta & Hl)".
    all: rewrite -> length_of_vals in *; try done.
    iSteps.
  Qed.

  Lemma wp_match l hdr x_fb e_fb brs e E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP e @ E {{ Φ }} -∗
    WP Match #l x_fb e_fb brs @ E {{ Φ }}.
  Proof.
    iIntros "%He >#Hl H".
    iApply wp_lift_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hσ Hl") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%_e %_σ %es %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_get_tag l hdr E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header_tag) -∗
    WP GetTag #l @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hσ Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%e %σ2 %es %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_get_size l hdr E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header_size) -∗
    WP GetSize #l @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_has_header_valid with "Hσ Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%e %σ2 %es %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_load l fld dq v E :
    {{{
      ▷ (l +ₗ fld) ↦{dq} v
    }}}
      Load #l #fld @ E
    {{{
      RET v;
      (l +ₗ fld) ↦{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iDestruct (state_interp_pointsto_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !> !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_store l fld w v E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Store #l #fld v @ E
    {{{
      RET ();
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iDestruct (state_interp_pointsto_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hσ Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wp_xchg l fld w v E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Xchg (#l, #fld)%V v @ E
    {{{
      RET w;
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iDestruct (state_interp_pointsto_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hσ Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma base_reducible_cas l fld v v1 v2 σ :
    σ.(state_heap) !! (l +ₗ fld) = Some v →
    base_reducible (CAS (#l, #fld)%V v1 v2) σ.
  Proof.
    destruct
      v as [[b0 | n0 | l0 | |] | | [] tag0 [| v0 vs0]],
      v1 as [[b1 | n1 | l1 | |] | | [] tag1 [| v1 vs1]].
    all: try (destruct (decide (b0 = b1)); first subst).
    all: try (destruct (decide (n0 = n1)); first subst).
    all: try (destruct (decide (l0 = l1)); first subst).
    all: try (destruct (decide (tag0 = tag1)); first subst).
    all: try (destruct (decide (v0 = v1)); first subst).
    all: try (destruct (decide (vs0 = vs1)); first subst).
    all: eauto with zoo.
  Qed.
  Lemma wp_cas l fld dq v v1 v2 E Φ :
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
    WP CAS (#l, #fld)%V v1 v2 @ E {{ Φ }}.
  Proof.
    iIntros ">Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iDestruct (state_interp_pointsto_valid with "Hσ Hl") as %Hlookup.
    iSplit. { iPureIntro. eapply base_reducible_cas; done. }
    iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    destruct
      v1 as [[b1 | n1 | l1 | |] | | [] tag1 [| v1 vs1]],
      v2 as [[b2 | n2 | l2 | |] | | [] tag2 [| v2 vs2]].
    all: try (destruct (decide (b1 = b2)); first subst).
    all: try (destruct (decide (n1 = n2)); first subst).
    all: try (destruct (decide (l1 = l2)); first subst).
    all: try (destruct (decide (tag1 = tag2)); first subst).
    all: try (destruct (decide (v1 = v2)); first subst).
    all: try (destruct (decide (vs1 = vs2)); first subst).
    all: invert_base_step; simplify; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iSteps
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)";
            iMod (state_interp_pointsto_update with "Hσ Hl") as "($ & Hl)";
            iSteps
        end
      end.
  Qed.
  Lemma wp_cas_suc l fld lit lit1 v2 E :
    literal_physical lit →
    lit = lit1 →
    {{{
      ▷ (l +ₗ fld) ↦ #lit
    }}}
      CAS (#l, #fld)%V #lit1 v2 @ E
    {{{
      RET #true;
      (l +ₗ fld) ↦ v2
    }}}.
  Proof.
    iIntros (Hlit <-) "%Φ >Hl HΦ".
    iApply (wp_cas with "Hl").
    destruct lit; [iSteps.. | done | done].
  Qed.

  Lemma wp_faa l fld (i1 i2 : Z) E :
    {{{
      ▷ (l +ₗ fld) ↦ #i1
    }}}
      FAA (#l, #fld)%V #i2 @ E
    {{{
      RET #i1;
      (l +ₗ fld) ↦ #(i1 + i2)
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iDestruct (state_interp_pointsto_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_pointsto_update with "Hσ Hl") as "($ & Hl)";
    iSteps.
  Qed.

  Lemma wp_fork e E Φ :
    ▷ WP e @ ⊤ {{ _, True }} -∗
    ▷ Φ ()%V -∗
    WP Fork e @ E {{ Φ }}.
  Proof.
    iIntros "H HΦ".
    iApply wp_lift_atomic_base_step; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit; first auto with zoo. iIntros "%v2 %σ2 %es %Hstep _ !> !> !>".
    invert_base_step.
    iSteps.
  Qed.

  Lemma wp_proph E :
    {{{
      True
    }}}
      Proph @ E
    {{{ prophs pid,
      RET #pid;
      prophet_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp_prophet_new with "Hσ") as "(%prophs & Hσ & Hpid)"; first done.
    iSteps.
  Qed.

  Lemma resolve_reducible e σ pid v :
    Atomic e →
    reducible e σ →
    reducible (Resolve e #pid v) σ.
  Proof.
    intros A (κ & e' & σ' & es & H).
    exists (κ ++ [(pid, (default v (to_val e'), v))]), e', σ', es.
    eapply (base_step_fill_prim_step' []); try done.
    assert (∃ w, Val w = e') as (w & <-).
    { unfold Atomic in A. apply (A σ e' κ σ' es) in H. unfold is_Some in H.
      destruct H as [w H]. exists w. simpl in H. apply (of_to_val _ _ H).
    }
    simpl. econstructor. apply prim_step_to_val_is_base_step. done.
  Qed.
  Lemma step_resolve e v1 v2 σ1 κ e2 σ2 es :
    Atomic e →
    prim_step (Resolve e v1 v2) σ1 κ e2 σ2 es →
    base_step (Resolve e v1 v2) σ1 κ e2 σ2 es.
  Proof.
    intros A [K e1' e2' Hfill -> step]. simpl in *.
    induction K as [| k K _] using rev_ind.
    - simpl in *. subst. invert_base_step. constructor. done.
    - rewrite fill_app /= in Hfill. destruct k; inversion Hfill; subst; clear Hfill.
      + assert (fill_item k (fill K e1') = fill (K ++ [k]) e1') as Heq1; first by rewrite fill_app.
        assert (fill_item k (fill K e2') = fill (K ++ [k]) e2') as Heq2; first by rewrite fill_app.
        rewrite fill_app /=. rewrite Heq1 in A.
        assert (is_Some (to_val (fill (K ++ [k]) e2'))) as H.
        { eapply (A σ1 _ κ σ2 es), (base_step_fill_prim_step' (K ++ [k])); done. }
        destruct H as [v H]. apply to_val_fill_some in H. destruct H, K; done.
      + rename select (of_val v1 = _) into Hv1.
        assert (to_val (fill K e1') = Some v1) as Hfill_v1 by rewrite -Hv1 //.
        apply to_val_fill_some in Hfill_v1 as (-> & ->).
        invert_base_step.
      + rename select (of_val v2 = _) into Hv2.
        assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
        apply to_val_fill_some in Hfill_v2 as (-> & ->).
        invert_base_step.
  Qed.
  Lemma wp_resolve e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_model pid prophs -∗
    WP e @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet_model pid prophs' -∗
      Φ res
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "%Hatomic %He Hpid H".
    rewrite !wp_unfold /wp_pre /= He. simpl in *.
    iIntros "%nt %σ1 %κ %κs Hσ".
    destruct κ as [| (pid' & (w' & v')) κ' _] using rev_ind.
    - iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep".
      exfalso. apply step_resolve in Hstep; last done.
      invert_base_step.
      destruct κ; done.
    - rewrite -assoc.
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep H£".
      apply step_resolve in Hstep; last done.
      invert_base_step. simplify_list_eq.
      iMod ("H" $! (Val w') σ2 es with "[%] H£") as "H".
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "H" as "(Hσ & H)".
      iMod (state_interp_prophet_resolve with "Hσ Hpid") as "(%prophs' & -> & $ & Hpid')".
      rewrite !wp_unfold /wp_pre /=.
      iDestruct "H" as "(HΦ & $)".
      iSteps.
  Qed.
End zoo_G.
