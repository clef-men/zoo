From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  tactics
  notations.
From zoo.language Require Export
  typeclasses.
From zoo.program_logic Require Export
  bwp.
From zoo Require Import
  options.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition wp_def e tid E Φ :=
    match tid with
    | None =>
        ∀ tid, BWP e ∶ tid @ E {{ Φ }}
    | Some tid =>
        BWP e ∶ tid @ E {{ Φ }}
    end%I.
  #[global] Arguments wp_def _ _%_E _ _%_I : assert.
End zoo_G.

#[local] Definition wp_aux : seal (@wp_def).
  Proof. by eexists. Qed.
Definition wp :=
  wp_aux.(unseal).
#[global] Arguments wp {_ _} _ _%_E _ _%_I : assert.
#[local] Lemma wp_unseal `{zoo_G : !ZooG Σ} :
  wp = wp_def.
Proof.
  rewrite -wp_aux.(seal_eq) //.
Qed.

#[local] Ltac wp_unseal :=
  rewrite wp_unseal /wp_def;
  select (option thread_id) (fun tid => destruct tid).

Declare Custom Entry wp_thread_id.
Notation "" := (
  None
)(in custom wp_thread_id
).
Notation "∶ tid" := (
  Some tid
)(in custom wp_thread_id at level 200,
  tid constr,
  format "'/  ' ∶  tid "
).
Notation "∷ tid" :=
  tid
( in custom wp_thread_id at level 200,
  tid constr,
  format "'/  ' ∷  tid "
).

Notation "'WP' e tid E {{ Φ } }" := (
  wp e%E tid E Φ%I
)(at level 20,
  e at level 200,
  tid custom wp_thread_id at level 200,
  E custom wp_mask at level 200,
  Φ at level 200,
  format "'[hv' WP  '/  ' '[' e ']'  tid E '/' {{  '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'WP' e tid E {{ v , Q } }" := (
  wp e%E tid E (λ v, Q%I)
)(at level 20,
  e at level 200,
  tid custom wp_thread_id at level 200,
  E custom wp_mask at level 200,
  v at level 200 as pattern,
  Q at level 200,
  format "'[hv' WP  '/  ' '[' e ']'  tid E '/' {{  '[' v ,  '/' Q ']'  '/' } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e tid E {{{ x1 .. xn , 'RET' v ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (∀ x1, .. (∀ xn, Q -∗ Φ (v : val)) ..) -∗
      wp e%E tid E Φ
  )%I
( at level 20,
  P at level 200,
  e at level 200,
  tid custom wp_thread_id at level 200,
  E custom wp_mask at level 200,
  x1 closed binder,
  xn closed binder,
  Q at level 200,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' e ']'  tid E '/' {{{  x1  ..  xn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } } ']'"
) : bi_scope.
Notation "'{{{' P } } } e tid E {{{ 'RET' v ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (Q -∗ Φ (v : val)) -∗
      wp e%E tid E Φ
  )%I
( at level 20,
  P at level 200,
  e at level 200,
  tid custom wp_thread_id at level 200,
  E custom wp_mask at level 200,
  Q at level 200,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' e ']'  tid E '/' {{{  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e tid E {{{ x1 .. xn , 'RET' v ; Q } } }" := (
  ∀ Φ,
  P%I -∗
  ▷ (∀ x1, .. (∀ xn, Q%I -∗ Φ (v : val)) ..) -∗
  wp e%E tid E Φ%I
) : stdpp_scope.
Notation "'{{{' P } } } e tid E {{{ 'RET' v ; Q } } }" := (
  ∀ Φ,
  P%I -∗
  ▷ (Q%I -∗ Φ (v : val)) -∗
  wp e%E tid E Φ%I
) : stdpp_scope.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ κs : list observation.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types P R : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  #[global] Instance wp_ne n e tid E :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    rewrite wp_unseal. solve_proper.
  Qed.
  #[global] Instance wp_proper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp e tid E).
  Proof.
    rewrite wp_unseal. solve_proper.
  Qed.
  #[global] Instance wp_contractive n e tid E :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    wp_unseal.
    - apply bwp_contractive.
    - intros He Φ1 Φ2 HΦ.
      f_equiv => tid.
      apply bwp_contractive; done.
  Qed.

  Lemma wp_thread_id_mono e tid E Φ :
    WP e @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    all: iSteps.
  Qed.

  Lemma wp_bwp e tid E Φ :
    WP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wp_unseal. iSteps.
  Qed.

  Lemma bwp_wp e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊢
    WP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wp_unseal //.
  Qed.
  Lemma bwp_wp_weak e tid E Φ :
    (∀ tid, BWP e ∶ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite -wp_thread_id_mono wp_unseal //.
  Qed.

  Lemma wp_state_interp e tid E Φ :
    ( ∀ nt σ κs,
      state_interp nt σ κs ={E}=∗
        state_interp nt σ κs ∗
        WP e ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_state_interp.
    - iIntros "H %tid".
      iApply bwp_state_interp. iIntros "%nt %σ %κs Hinterp".
      iMod ("H" with "Hinterp") as "($ & H)".
      iSteps.
  Qed.

  Lemma wp_value_fupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_value_fupd'.
    - iIntros "H %tid".
      iApply (bwp_value_fupd' with "H").
  Qed.
  Lemma wp_value_fupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wp_value_fupd' => <- //.
  Qed.
  Lemma wp_value' v tid E Φ :
    Φ v ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (wp_value_fupd' with "HΦ").
  Qed.
  Lemma wp_value e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wp_value' => <- //.
  Qed.

  Lemma wp_value_mono v tid E Φ1 Φ2 :
    WP of_val v ∷ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    WP of_val v ∷ tid @ E {{ Φ2 }}.
  Proof.
    wp_unseal.
    - apply bwp_value_mono.
    - iIntros "H HΦ %tid".
      iApply (bwp_value_mono with "H HΦ").
  Qed.

  Lemma wp_strong_mono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    WP e ∷ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    WP e ∷ tid @ E2 {{ Φ2 }}.
  Proof.
    wp_unseal.
    - apply bwp_strong_mono.
    - iIntros "%HE H HΦ %tid".
      iApply (bwp_strong_mono with "H HΦ"); first done.
  Qed.
  Lemma wp_mono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    WP e ∷ tid @ E {{ Φ1 }} ⊢
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (wp_strong_mono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance wp_mono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply wp_mono. done.
  Qed.
  #[global] Instance wp_flip_mono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupd_wp e tid E Φ :
    (|={E}=> WP e ∷ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply fupd_bwp.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (fupd_bwp with "H").
  Qed.
  Lemma wp_fupd e tid E Φ :
    WP e ∷ tid @ E {{ v, |={E}=> Φ v }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp_frame_l e tid E Φ R :
    R ∗ WP e ∷ tid @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp_frame_r e tid E Φ R :
    WP e ∷ tid @ E {{ Φ }} ∗ R ⊢
    WP e ∷ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp_wand {e tid E} Φ1 Φ2 :
    WP e ∷ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp_frame_wand e tid E Φ R :
    R -∗
    WP e ∷ tid @ E {{ v, R -∗ Φ v }} -∗
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (wp_wand with "H").
    iSteps.
  Qed.

  Lemma wp_atomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> WP e ∷ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    WP e ∷ tid @ E1 {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_atomic; first done.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp_atomic with "H").
  Qed.

  Lemma wp_step_fupd e tid E1 E2 P Φ :
    TCEq (to_val e) None →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗
    WP e ∷ tid @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e ∷ tid @ E1 {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_step_fupd.
    - iIntros "%He %HE HP H %tid".
      iApply (bwp_step_fupd with "HP H"); first done.
  Qed.

  Lemma wp_bind K `{!Context K} e tid1 tid2 E Φ :
    ( if tid2 is Some tid2 then
        if tid1 is Some tid1 then
          tid1 = tid2
        else
          False
      else
        True
    ) →
    WP e ∷ tid2 @ E {{ v, WP K (of_val v) ∷ tid1 @ E {{ Φ }} }} ⊢
    WP K e ∷ tid1 @ E {{ Φ }}.
  Proof.
    wp_unseal; destruct tid1 as [tid1 |].
    - intros ->.
      apply bwp_bind; first done.
    - done.
    - iIntros "_ H".
      iApply (bwp_bind with "H").
    - iIntros "_ H %tid".
      iApply bwp_bind.
      iApply (bwp_wand with "H").
      iSteps.
  Qed.
  Lemma wp_bind' K `{!Context K} e tid E Φ :
    WP e ∷ tid @ E {{ v, WP K (of_val v) ∷ tid @ E {{ Φ }} }} ⊢
    WP K e ∷ tid @ E {{ Φ }}.
  Proof.
    apply: wp_bind.
    destruct tid; done.
  Qed.

  #[global] Instance frame_wp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (WP e ∷ tid @ E {{ Φ1 }})
      (WP e ∷ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame wp_frame_l => HR.
    apply wp_mono, HR.
  Qed.

  #[global] Instance is_except_0_wp e tid E Φ :
    IsExcept0 (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modal_bupd_wp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.

  #[global] Instance elim_modal_fupd_wp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.
  #[global] Instance elim_modal_fupd_wp_wrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_wp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2}=> P)
      False
      (WP e ∷ tid @ E1 {{ Φ }})
      False
  | 100.
  Proof.
    intros [].
  Qed.

  #[global] Instance elim_modal_fupd_wp_atomic p e tid E1 E2 P Φ :
    ElimModal
      (Atomic e)
      p
      false
      (|={E1,E2}=> P)
      P
      (WP e ∷ tid @ E1 {{ Φ }})
      (WP e ∷ tid @ E2 {{ v, |={E2,E1}=> Φ v }})%I
  | 100.
  Proof.
    intros He.
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp_atomic //.
  Qed.
  #[global] Instance elim_modal_fupd_wp_atomic_wrong_mask p e tid E1 E2 E2' P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2,E2'}=> P)
      False
      (WP e ∷ tid @ E1 {{ Φ }})
      False
  | 200.
  Proof.
    intros [].
  Qed.

  #[global] Instance add_modal_fupd_wp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.

  #[global] Instance elim_acc_wp_atomic {X} e tid E1 E2 α β γ Φ :
    ElimAcc (X := X)
      (Atomic e)
      (fupd E1 E2)
      (fupd E2 E1)
      α
      β
      γ
      (WP e ∷ tid @ E1 {{ Φ }})
      (λ x, WP e ∷ tid @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I
  | 100.
  Proof.
    iIntros "%He Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply (wp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_acc_wp_nonatomic {X} e tid E α β γ Φ :
    ElimAcc (X := X)
      True
      (fupd E E)
      (fupd E E)
      α
      β
      γ
      (WP e ∷ tid @ E {{ Φ }})
      (λ x, WP e ∷ tid @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma wp_pure_step_later ϕ n e1 e2 tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ▷^n (
      £ (n * num_later_per_step) -∗
      WP e2 ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e1 ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply bwp_pure_step_later.
    - iIntros "%Hexec %Hϕ H %tid".
      iApply bwp_pure_step_later; first done.
      iSteps.
  Qed.
End zoo_G.

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
        Φ false%V
      ) ∧ (
        ⌜v1 ≈ v2⌝ -∗
        Φ true%V
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

  Lemma wp_match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x_fb e_fb brs = Some e →
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
  Lemma wp_match_context K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP K e ∷ tid @ E {{ Φ }} -∗
    WP K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}.
  Proof.
    wp_unseal.
    - apply: bwp_match_context.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp_match_context with "Hl H"); first done.
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
        Φ false%V
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦{dq} v -∗
          ⌜dq = DfracOwn 1⌝ ∗
          (l +ₗ fld) ↦{dq} v ∗
          ( (l +ₗ fld) ↦ v2 -∗
            Φ true%V
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
        Φ false%V
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦ v2 -∗
        Φ true%V
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
