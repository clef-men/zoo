From iris.base_logic Require Export
  lib.fancy_updates.

From zebre Require Import
  prelude.
From zebre.iris Require Import
  diaframe.
From zebre.iris.program_logic Require Export
  language.
From zebre Require Import
  options.

Class IrisG Λ Σ := {
  #[global] iris_G_inv_G :: invGS Σ ;
  state_interp : state Λ → list (observation Λ) → iProp Σ ;
  fork_post : val Λ → iProp Σ ;
}.
#[global] Arguments Build_IrisG {_ _ _} _ _ : assert.
#[global] Opaque iris_G_inv_G.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Definition wp_pre (wp : expr Λ -d> coPset -d> (val Λ -d> iPropO Σ) -d> iPropO Σ)
  : expr Λ -d> coPset -d> (val Λ -d> iPropO Σ) -d> iPropO Σ
  :=
    λ e E Φ,
      match to_val e with
      | Some v =>
          |={E}=> Φ v
      | None =>
          ∀ σ κ κs,
          state_interp σ (κ ++ κs) -∗
            |={E, ∅}=>
            ⌜reducible e σ⌝ ∗
              ∀ e' σ' es ϕ,
              ⌜prim_step e σ κ e' σ' es ϕ⌝ -∗
              ⌜ϕ⌝ -∗
              £ 1 -∗
                |={∅}=> ▷ |={∅, E}=>
                state_interp σ' κs ∗
                wp e' E Φ ∗
                [∗ list] i ↦ e ∈ es,
                  wp e ⊤ fork_post
      end%I.
  #[global] Arguments wp_pre _ e%E E Φ%I : rename.

  #[local] Instance wp_pre_contractive :
    Contractive wp_pre.
  Proof.
    rewrite /wp_pre /= => n wp1 wp2 Hwp e E Φ.
    repeat (apply Hwp || f_contractive || f_equiv).
  Qed.

  #[local] Definition wp_def :=
    fixpoint wp_pre.
  #[global] Arguments wp_def e%E E Φ%I : rename.
End iris_G.

#[local] Definition wp_aux : seal (@wp_def).
  Proof. by eexists. Qed.
Definition wp :=
  wp_aux.(unseal).
#[global] Arguments wp {_ _ _} e%E E Φ%I : rename.
#[local] Lemma wp_unseal `{iris_G : !IrisG Λ Σ} :
  wp = @wp_def Λ Σ _.
Proof.
  rewrite -wp_aux.(seal_eq) //.
Qed.

Notation "'WP' e @ E {{ Φ } }" := (
  wp e%E E Φ
)(at level 20,
  e, Φ at level 200,
  only parsing
) : bi_scope.
Notation "'WP' e {{ Φ } }" := (
  wp e%E ⊤ Φ
)(at level 20,
  e, Φ at level 200,
  only parsing
) : bi_scope.

Notation "'WP' e @ E {{ v , Q } }" := (
  wp e%E E (λ v, Q)
)(at level 20,
  e, Q at level 200,
  format "'[hv' 'WP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'"
) : bi_scope.
Notation "'WP' e {{ v , Q } }" := (
  wp e%E ⊤ (λ v, Q)
)(at level 20,
  e, Q at level 200,
  format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) ..) -∗
      WP e @ E {{ Φ }}
  )%I
( at level 20,
  x closed binder,
  y closed binder,
  format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'"
) : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) ..) -∗
      WP e {{ Φ }}
  )%I
( at level 20,
  x closed binder,
  y closed binder,
  format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (Q -∗ Φ pat%V) -∗
      WP e @ E {{ Φ }}
  )%I
( at level 20,
  format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'"
) : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (Q -∗ Φ pat%V) -∗
      WP e {{ Φ }}
  )%I
( at level 20,
  format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" := (
  ∀ Φ,
  P -∗
  ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) ..) -∗
  WP e @ E {{ Φ }}
) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" := (
  ∀ Φ,
  P -∗
  ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) ..) -∗
  WP e {{ Φ }}
) : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" := (
  ∀ Φ,
  P -∗
  ▷ (Q -∗ Φ pat%V) -∗
  WP e @ E {{ Φ }}
) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" := (
  ∀ Φ,
  P -∗
  ▷ (Q -∗ Φ pat%V) -∗
  WP e {{ Φ }}
) : stdpp_scope.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types P R : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma wp_unfold e E Φ :
    WP e @ E {{ Φ }} ⊣⊢
    wp_pre wp e E Φ.
  Proof.
    rewrite wp_unseal. apply (fixpoint_unfold wp_pre).
  Qed.

  #[global] Instance wp_ne n e E :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (wp e E).
  Proof.
    move: e. induction (lt_wf n) as [n _ IH] => e Φ1 Φ2 HΦ.
    rewrite !wp_unfold /wp_pre /=.
    do 26 (f_contractive || f_equiv).
    apply IH; first done.
    f_equiv.
    eapply dist_le; [apply HΦ | lia].
  Qed.
  #[global] Instance wp_proper e E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp e E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply equiv_dist => n. apply wp_ne => v. apply equiv_dist. done.
  Qed.
  #[global] Instance wp_contractive n e E :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (wp e E).
  Proof.
    intros He Φ1 Φ2 HΦ.
    rewrite !wp_unfold /wp_pre He /=.
    repeat (f_contractive || f_equiv).
  Qed.

  Lemma wp_value_fupd' v E Φ :
    WP of_val v @ E {{ Φ }} ⊣⊢
    |={E}=> Φ v.
  Proof.
    rewrite wp_unfold /wp_pre to_of_val //.
  Qed.
  Lemma wp_value_fupd e v E Φ :
    AsVal e v →
    WP e @ E {{ Φ }} ⊣⊢
    |={E}=> Φ v.
  Proof.
    rewrite -wp_value_fupd' => <- //.
  Qed.
  Lemma wp_value' v E Φ :
    Φ v ⊢
    WP (of_val v) @ E {{ Φ }}.
  Proof.
    rewrite wp_value_fupd'. auto.
  Qed.
  Lemma wp_value e v E Φ :
    AsVal e v →
    Φ v ⊢
    WP e @ E {{ Φ }}.
  Proof.
    rewrite wp_value' => <- //.
  Qed.

  Lemma wp_strong_mono e E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    WP e @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    WP e @ E2 {{ Φ2 }}.
  Proof.
    iIntros "%HE H HΦ".
    iLöb as "HLöb" forall (e).
    rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e) as [v |] eqn:He.
    - iApply ("HΦ" with "[> H]").
      iSteps.
    - iIntros "%σ1 %κ %κs Hσ".
      iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iModIntro. iStep. iIntros "%e2 %σ2 %es %ϕ %Hstep %Hϕ H£".
      iMod ("H" with "[//] [//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "($ & H & Hes)".
      iMod "Hclose" as "_".
      iSplitR "Hes"; iSteps.
  Qed.
  Lemma wp_mono e E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    WP e @ E {{ Φ1 }} ⊢
    WP e @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (wp_strong_mono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  Lemma wp_mask_mono e E1 E2 Φ :
    E1 ⊆ E2 →
    WP e @ E1 {{ Φ }} ⊢
    WP e @ E2 {{ Φ }}.
  Proof.
    iIntros "%HE H".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  #[global] Instance wp_mono' e E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp e E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply wp_mono. done.
  Qed.
  #[global] Instance wp_flip_mono' e E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp e E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupd_wp e E Φ :
    (|={E}=> WP e @ E {{ Φ }}) ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) as [v |] eqn:He; first iSteps.
    iIntros "%σ1 %κ %κs Hσ".
    iMod "H".
    iApply ("H" with "Hσ").
  Qed.
  Lemma wp_fupd e E Φ :
    WP e @ E {{ v, |={E}=> Φ v }} ⊢
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp_atomic e `{!Atomic e} E1 E2 Φ :
    (|={E1, E2}=> WP e @ E2 {{ v, |={E2, E1}=> Φ v }}) ⊢
    WP e @ E1 {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v |] eqn:He; first iSteps.
    iIntros "%σ1 %κ1 %κs Hσ".
    iMod "H".
    iMod ("H" $! σ1 with "Hσ") as "($ & H)".
    iModIntro. iIntros "%e2 %σ2 %es1 %ϕ1 %Hstep1 %Hϕ1 H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(Hσ & H & Hes)".
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e2) as [v2 |] eqn:He2.
    - iDestruct "H" as ">>$".
      iSteps.
    - iMod ("H" $! _ [] with "Hσ") as "(%Hreducible2 & _)".
      destruct Hreducible2 as (κ2 & e3 & σ3 & es2 & ϕ2 & Hstep2).
      edestruct atomic; [done | congruence].
  Qed.

  Lemma wp_step_fupd e E1 E2 P Φ :
    TCEq (to_val e) None →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗
    WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @ E1 {{ Φ }}.
  Proof.
    rewrite !wp_unfold /wp_pre /=.
    iIntros (-> HE) "HP H %σ1 %κ1 %κs Hσ".
    iMod "HP".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e2 %σ2 %es1 %ϕ1 %Hstep %Hϕ H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "($ & H & $)".
    iMod "HP".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp_bind K `{!LanguageCtx K} e E Φ :
    WP e @ E {{ v, WP K (of_val v) @ E {{ Φ }} }} ⊢
    WP K e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      iApply (fupd_wp with "H").
    - rewrite wp_unfold /wp_pre fill_not_val //.
      iIntros "%σ1 %κ1 %κs Hσ".
      iMod ("H" with "Hσ") as "(%Hreducible1 & H)".
      iModIntro; iSplit; first eauto using reducible_fill.
      iIntros "%e2 %σ2 %es1 %ϕ1 %Hstep1 %Hϕ1 H£".
      destruct (fill_step_inv e σ1 κ1 e2 σ2 es1 ϕ1) as (e2' & -> & Hstep1'); [done.. |].
      iMod ("H" with "[//] [//] H£") as "H".
      iModIntro. iSteps.
  Qed.

  Lemma wp_bind_inv K `{!LanguageCtx K} e E Φ :
    WP K e @ E {{ Φ }} ⊢
    WP e @ E {{ v, WP K (of_val v) @ E {{ Φ }} }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      rewrite !wp_unfold /wp_pre //.
    - rewrite fill_not_val //.
      iIntros "%σ1 %κ1 %κs Hσ".
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iModIntro; iSplit; first eauto using reducible_fill_inv.
      iIntros "%e2 %σ2 %es1 %ϕ1 %Hstep1 %Hϕ1 H£".
      iMod ("H" with "[] [//] H£") as "H"; first eauto using fill_step.
      iModIntro. iSteps.
  Qed.

  Lemma wp_frame_l e E Φ R :
    R ∗ WP e @ E {{ Φ }} ⊢
    WP e @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp_frame_r e E Φ R :
    WP e @ E {{ Φ }} ∗ R ⊢
    WP e @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp_wand e E Φ1 Φ2 :
    WP e @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WP e @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (wp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp_wand_l e E Φ1 Φ2 :
    (∀ v, Φ1 v -∗ Φ2 v) ∗ WP e @ E {{ Φ1 }} ⊢
    WP e @ E {{ Φ2 }}.
  Proof.
    iIntros "(HΦ & H)".
    iApply (wp_wand with "H HΦ").
  Qed.
  Lemma wp_wand_r e E Φ1 Φ2 :
    WP e @ E {{ Φ1 }} ∗ (∀ v, Φ1 v -∗ Φ2 v) ⊢
    WP e @ E {{ Φ2 }}.
  Proof.
    iIntros "(H & HΦ)".
    iApply (wp_wand with "H HΦ").
  Qed.
  Lemma wp_frame_wand e E Φ R :
    R -∗
    WP e @ E {{ v, R -∗ Φ v }} -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (wp_wand with "H").
    iSteps.
  Qed.

  #[global] Instance frame_wp p e E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (WP e @ E {{ Φ1 }})
      (WP e @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame wp_frame_l => HR.
    apply wp_mono, HR.
  Qed.

  #[global] Instance is_except_0_wp e E Φ :
    IsExcept0 (WP e @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modal_bupd_wp p e E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (WP e @ E {{ Φ }})
      (WP e @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.

  #[global] Instance elim_modal_fupd_wp p e E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (WP e @ E {{ Φ }})
      (WP e @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.
  #[global] Instance elim_modal_fupd_wp_wrong_mask p e E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_wp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2}=> P)
      False
      (WP e @ E1 {{ Φ }})
      False
  | 100.
  Proof.
    intros [].
  Qed.

  #[global] Instance elim_modal_fupd_wp_atomic p e E1 E2 P Φ :
    ElimModal
      (Atomic e)
      p
      false
      (|={E1,E2}=> P)
      P
      (WP e @ E1 {{ Φ }})
      (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I
  | 100.
  Proof.
    intros He.
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp_atomic //.
  Qed.
  #[global] Instance elim_modal_fupd_wp_atomic_wrong_mask p e E1 E2 E2' P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2,E2'}=> P)
      False
      (WP e @ E1 {{ Φ }})
      False
  | 200.
  Proof.
    intros [].
  Qed.

  #[global] Instance add_modal_fupd_wp e E P Φ :
    AddModal
      (|={E}=> P)
      P
      (WP e @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp //.
  Qed.

  #[global] Instance elim_acc_wp_atomic {X} e E1 E2 α β γ Φ :
    ElimAcc (X := X)
      (Atomic e)
      (fupd E1 E2)
      (fupd E2 E1)
      α
      β
      γ
      (WP e @ E1 {{ Φ }})
      (λ x, WP e @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I
  | 100.
  Proof.
    iIntros "%He Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply (wp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_acc_wp_nonatomic {X} e E α β γ Φ :
    ElimAcc (X := X)
      True
      (fupd E E)
      (fupd E E)
      α
      β
      γ
      (WP e @ E {{ Φ }})
      (λ x, WP e @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End iris_G.
