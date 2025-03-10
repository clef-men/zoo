From iris.base_logic Require Export
  lib.fancy_updates.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Export
  language.
From zoo Require Import
  options.

Class IrisG Λ Σ := {
  #[global] iris_G_inv_G :: invGS Σ ;
  state_interp : nat → state Λ → list (observation Λ) → iProp Σ ;
  fork_post : val Λ → iProp Σ ;
}.
#[global] Arguments Build_IrisG {_ _ _} _ _ : assert.
#[global] Opaque iris_G_inv_G.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Definition bwp_pre (bwp : expr Λ -d> thread_id -d> coPset -d> (val Λ -d> iPropO Σ) -d> iPropO Σ)
  : expr Λ -d> thread_id -d> coPset -d> (val Λ -d> iPropO Σ) -d> iPropO Σ
  :=
    λ e tid E Φ,
      match to_val e with
      | Some v =>
          |={E}=> Φ v
      | None =>
          ∀ nt σ κ κs,
          state_interp nt σ (κ ++ κs) -∗
            |={E,∅}=>
            ⌜reducible tid e σ⌝ ∗
              ∀ e' σ' es,
              ⌜prim_step tid e σ κ e' σ' es⌝ -∗
              £ 1 -∗
                |={∅}=> ▷ |={∅,E}=>
                state_interp (nt + length es) σ' κs ∗
                bwp e' tid E Φ ∗
                [∗ list] i ↦ e ∈ es,
                  bwp e (nt + i) ⊤ fork_post
      end%I.
  #[global] Arguments bwp_pre bwp e%_E tid E Φ%_I : rename.

  #[local] Instance bwp_pre_contractive :
    Contractive bwp_pre.
  Proof.
    rewrite /bwp_pre /= => n bwp1 bwp2 Hbwp e tid E Φ.
    repeat (apply Hbwp || f_contractive || f_equiv).
  Qed.

  #[local] Definition bwp_def :=
    fixpoint bwp_pre.
  #[global] Arguments bwp_def e%_E tid E Φ%_I : rename.
End iris_G.

#[local] Definition bwp_aux : seal (@bwp_def).
  Proof. by eexists. Qed.
Definition bwp :=
  bwp_aux.(unseal).
#[global] Arguments bwp {_ _ _} e%_E tid E Φ%_I : rename.
#[local] Lemma bwp_unseal `{iris_G : !IrisG Λ Σ} :
  bwp = @bwp_def Λ Σ _.
Proof.
  rewrite -bwp_aux.(seal_eq) //.
Qed.

Declare Custom Entry wp_mask.
Notation "" := (
  @top coPset _
)(in custom wp_mask
).
Notation "@ E" :=
  E
( in custom wp_mask at level 200,
  E constr,
  format "'/  ' @  E "
).

Notation "'BWP' e ∶ tid E {{ Φ } }" := (
  bwp e%E tid E Φ%I
)(at level 20,
  e at level 200,
  tid at level 200,
  E custom wp_mask at level 200,
  Φ at level 200,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BWP' e ∶ tid E {{ v , Q } }" := (
  bwp e%E tid E (λ v, Q%I)
)(at level 20,
  e at level 200,
  tid at level 200,
  E custom wp_mask at level 200,
  Q at level 200,
  v at level 200 as pattern,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' v ,  '/' Q ']'  '/' } } ']'"
) : bi_scope.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types P R : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma bwp_unfold e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊣⊢
    bwp_pre bwp e tid E Φ.
  Proof.
    rewrite bwp_unseal. apply (fixpoint_unfold bwp_pre).
  Qed.

  #[global] Instance bwp_ne n e tid E :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    move: e. induction (lt_wf n) as [n _ IH] => e Φ1 Φ2 HΦ.
    rewrite !bwp_unfold /bwp_pre /=.
    do 25 (f_contractive || f_equiv).
    apply IH; first done.
    f_equiv.
    eapply dist_le; [apply HΦ | lia].
  Qed.
  #[global] Instance bwp_proper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply equiv_dist => n. apply bwp_ne => v. apply equiv_dist. done.
  Qed.
  #[global] Instance bwp_contractive n e tid E :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    intros He Φ1 Φ2 HΦ.
    rewrite !bwp_unfold /bwp_pre He /=.
    repeat (f_contractive || f_equiv).
  Qed.

  Lemma bwp_value_fupd' v tid E Φ :
    BWP of_val v ∶ tid @ E {{ Φ }} ⊣⊢
    |={E}=> Φ v.
  Proof.
    rewrite bwp_unfold /bwp_pre to_of_val //.
  Qed.
  Lemma bwp_value_fupd e v tid E Φ :
    AsVal e v →
    BWP e ∶ tid @ E {{ Φ }} ⊣⊢
    |={E}=> Φ v.
  Proof.
    rewrite -bwp_value_fupd' => <- //.
  Qed.
  Lemma bwp_value' v tid E Φ :
    Φ v ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_value_fupd'. auto.
  Qed.
  Lemma bwp_value e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_value' => <- //.
  Qed.

  Lemma bwp_strong_mono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    BWP e ∶ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    BWP e ∶ tid @ E2 {{ Φ2 }}.
  Proof.
    iIntros "%HE H HΦ".
    iLöb as "HLöb" forall (e).
    rewrite !bwp_unfold /bwp_pre /=.
    destruct (to_val e) as [v |] eqn:He.
    - iApply ("HΦ" with "[> H]").
      iSteps.
    - iIntros "%nt %σ1 %κ %κs Hσ".
      iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iModIntro. iStep. iIntros "%e2 %σ2 %es %Hstep H£".
      iMod ("H" with "[//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "($ & H & Hes)".
      iMod "Hclose" as "_".
      iSplitR "Hes"; iSteps.
  Qed.
  Lemma bwp_mono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    BWP e ∶ tid @ E {{ Φ1 }} ⊢
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (bwp_strong_mono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance bwp_mono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply bwp_mono. done.
  Qed.
  #[global] Instance bwp_flip_mono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (bwp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupd_bwp e tid E Φ :
    (|={E}=> BWP e ∶ tid @ E {{ Φ }}) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite bwp_unfold /bwp_pre.
    destruct (to_val e) as [v |] eqn:He; first iSteps.
    iIntros "%nt %σ1 %κ %κs Hσ".
    iMod "H".
    iApply ("H" with "Hσ").
  Qed.
  Lemma bwp_fupd e tid E Φ :
    BWP e ∶ tid @ E {{ v, |={E}=> Φ v }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (bwp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwp_frame_l e tid E Φ R :
    R ∗ BWP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (bwp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwp_frame_r e tid E Φ R :
    BWP e ∶ tid @ E {{ Φ }} ∗ R ⊢
    BWP e ∶ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (bwp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwp_wand {e tid E} Φ1 Φ2 :
    BWP e ∶ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    BWP e ∶ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (bwp_strong_mono with "H"); first done.
    iSteps.
  Qed.
  Lemma bwp_frame_wand e tid E Φ R :
    R -∗
    BWP e ∶ tid @ E {{ v, R -∗ Φ v }} -∗
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (bwp_wand with "H").
    iSteps.
  Qed.

  Lemma bwp_atomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> BWP e ∶ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite !bwp_unfold /bwp_pre.
    destruct (to_val e) as [v |] eqn:He; first iSteps.
    iIntros "%nt %σ1 %κ1 %κs Hσ".
    iMod "H".
    iMod ("H" with "Hσ") as "($ & H)".
    iModIntro. iIntros "%e2 %σ2 %es1 %Hstep1 H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(Hσ & H & Hes)".
    rewrite !bwp_unfold /bwp_pre.
    destruct (to_val e2) as [v2 |] eqn:He2.
    - iDestruct "H" as ">>$".
      iSteps.
    - iMod ("H" $! _ _ [] with "Hσ") as "(%Hreducible2 & _)".
      destruct Hreducible2 as (κ2 & e3 & σ3 & es2 & Hstep2).
      edestruct atomic; [done | congruence].
  Qed.

  Lemma bwp_step_fupd e tid E1 E2 P Φ :
    TCEq (to_val e) None →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗
    BWP e ∶ tid @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    rewrite !bwp_unfold /bwp_pre /=.
    iIntros (-> HE) "HP H %nt %σ1 %κ1 %κs Hσ".
    iMod "HP".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e2 %σ2 %es1 %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "($ & H & $)".
    iMod "HP".
    iApply (bwp_strong_mono with "H"); first done.
    iSteps.
  Qed.

  Lemma bwp_bind K `{!LanguageCtx K} e tid E Φ :
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }} ⊢
    BWP K e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite bwp_unfold /bwp_pre.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      iApply (fupd_bwp with "H").
    - rewrite bwp_unfold /bwp_pre fill_not_val //.
      iIntros "%nt %σ1 %κ1 %κs Hσ".
      iMod ("H" with "Hσ") as "(%Hreducible1 & H)".
      iModIntro; iSplit; first eauto using reducible_fill.
      iIntros "%e2 %σ2 %es1 %Hstep1 H£".
      destruct (fill_step_inv tid e σ1 κ1 e2 σ2 es1) as (e2' & -> & Hstep1'); [done.. |].
      iMod ("H" with "[//] H£") as "H".
      iModIntro. iSteps.
  Qed.

  Lemma bwp_bind_inv K `{!LanguageCtx K} e tid E Φ :
    BWP K e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite !bwp_unfold /bwp_pre /=.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      rewrite !bwp_unfold /bwp_pre //.
    - rewrite fill_not_val //.
      iIntros "%nt %σ1 %κ1 %κs Hσ".
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iModIntro; iSplit; first eauto using reducible_fill_inv.
      iIntros "%e2 %σ2 %es1 %Hstep1 H£".
      iMod ("H" with "[] H£") as "H"; first eauto using fill_step.
      iModIntro. iSteps.
  Qed.

  #[global] Instance frame_bwp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (BWP e ∶ tid @ E {{ Φ1 }})
      (BWP e ∶ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame bwp_frame_l => HR.
    apply bwp_mono, HR.
  Qed.

  #[global] Instance is_except_0_bwp e tid E Φ :
    IsExcept0 (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd_bwp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modal_bupd_bwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_bwp //.
  Qed.

  #[global] Instance elim_modal_fupd_bwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }})
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd_bwp //.
  Qed.
  #[global] Instance elim_modal_fupd_bwp_wrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_bwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2}=> P)
      False
      (BWP e ∶ tid @ E1 {{ Φ }})
      False
  | 100.
  Proof.
    intros [].
  Qed.

  #[global] Instance elim_modal_fupd_bwp_atomic p e tid E1 E2 P Φ :
    ElimModal
      (Atomic e)
      p
      false
      (|={E1,E2}=> P)
      P
      (BWP e ∶ tid @ E1 {{ Φ }})
      (BWP e ∶ tid @ E2 {{ v, |={E2,E1}=> Φ v }})%I
  | 100.
  Proof.
    intros He.
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r bwp_atomic //.
  Qed.
  #[global] Instance elim_modal_fupd_bwp_atomic_wrong_mask p e tid E1 E2 E2' P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2,E2'}=> P)
      False
      (BWP e ∶ tid @ E1 {{ Φ }})
      False
  | 200.
  Proof.
    intros [].
  Qed.

  #[global] Instance add_modal_fupd_bwp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (BWP e ∶ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_bwp //.
  Qed.

  #[global] Instance elim_acc_bwp_atomic {X} e tid E1 E2 α β γ Φ :
    ElimAcc (X := X)
      (Atomic e)
      (fupd E1 E2)
      (fupd E2 E1)
      α
      β
      γ
      (BWP e ∶ tid @ E1 {{ Φ }})
      (λ x, BWP e ∶ tid @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I
  | 100.
  Proof.
    iIntros "%He Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply (bwp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_acc_bwp_nonatomic {X} e tid E α β γ Φ :
    ElimAcc (X := X)
      True
      (fupd E E)
      (fupd E E)
      α
      β
      γ
      (BWP e ∶ tid @ E {{ Φ }})
      (λ x, BWP e ∶ tid @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply bwp_fupd.
    iApply (bwp_wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End iris_G.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma bwp_lift_step e tid E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            state_interp (nt + length es) σ' κs ∗
            BWP e' ∶ tid @ E {{ Φ }} ∗
            [∗ list] i ↦ e ∈ es,
              BWP e ∶ nt + i {{ fork_post }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_unfold /bwp_pre => -> //.
  Qed.
  Lemma bwp_lift_step_nofork e tid E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            BWP e' ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_atomic_step e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            state_interp (nt + length es) σ' κs ∗
            from_option Φ False (to_val e') ∗
            [∗ list] i ↦ e ∈ es,
              BWP e ∶ nt + i {{ fork_post }}
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose %e' %σ' %es %Hstep H£".
    iMod "Hclose" as "_".
    iMod ("H" with "[//] H£") as "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_".
    iMod "H" as "($ & HΦ & $)".
    destruct (to_val e') eqn:He'; last by iExFalso.
    iApply (bwp_value with "HΦ").
    apply of_to_val. done.
  Qed.
  Lemma bwp_lift_atomic_step_nofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            from_option Φ False (to_val e')
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_pure_step_nofork `{!Inhabited (state Λ)} e tid E1 E2 Φ :
    ( ∀ σ,
      reducible tid e σ
    ) →
    ( ∀ σ κ e' σ' es,
      prim_step tid e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜prim_step tid e σ κ e' σ es⌝ -∗
      £ 1 -∗
      BWP e' ∶ tid @ E1 {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply bwp_lift_step.
    { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
    iIntros "%nt %σ %κ %κs Hσ".
    iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep H£ !> !>".
    edestruct Hpure as (? & ? & ?); first done. subst.
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_pure_det_step_nofork `{!Inhabited (state Λ)} e1 e2 tid E1 E2 Φ :
    ( ∀ σ1,
      reducible tid e1 σ1
    ) →
    ( ∀ σ1 κ e2' σ2 es,
      prim_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      £ 1 -∗
      BWP e2 ∶ tid @ E1 {{ Φ }}
    ) ⊢
    BWP e1 ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply (bwp_lift_pure_step_nofork); [done | naive_solver |].
    iApply (step_fupd_wand with "H"). iIntros "H %σ1 %e2' %κ %es %Hstep H£".
    apply Hpure in Hstep as (-> & _ & -> & ->).
    iSteps.
  Qed.

  Lemma bwp_pure_step `{!Inhabited (state Λ)} ϕ n e1 e2 tid E1 E2 Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ( |={E1}[E2]▷=>^n
      £ n -∗
      BWP e2 ∶ tid @ E1 {{ Φ }}
    ) ⊢
    BWP e1 ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hϕ H".
    specialize (Hexec Hϕ).
    iInduction Hexec as [e | n e1 e2 e3 (Hsafe & Hpure)] "IH" => /=.
    - iMod lc_zero as "H£".
      iSteps.
    - iApply bwp_lift_pure_det_step_nofork.
      + eauto using reducible_no_obs_reducible.
      + naive_solver.
      + iApply (step_fupd_wand with "H"). iIntros "H H£".
        iApply "IH".
        iApply (step_fupdN_wand with "H").
        rewrite (lc_succ n). iSteps.
  Qed.
  Lemma bwp_pure_step_later `{!Inhabited (state Λ)} ϕ n tid e1 e2 E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ▷^n (
      £ n -∗
      BWP e2 ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e1 ∶ tid @ E {{ Φ }}.
  Proof.
    intros Hexec Hϕ.
    rewrite -bwp_pure_step // {Hexec}.
    enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as H by apply H.
    intros P. induction n as [| n IH]; rewrite //= -step_fupd_intro // IH //.
  Qed.
End iris_G.

From zoo.iris.program_logic Require Import
  ectx_language.

Section iris_G.
  Context {Λ : ectx_language} `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  #[local] Hint Resolve
    base_reducible_reducible
    base_reducible_prim_step
  : core.

  Lemma bwp_lift_base_step e tid E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            state_interp (nt + length es) σ' κs ∗
            BWP e' ∶ tid @ E {{ Φ }} ∗
            [∗ list] i ↦ e ∈ es,
              BWP e ∶ nt + i {{ fork_post }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep".
    iApply ("H" with "[%]").
    naive_solver.
  Qed.
  Lemma bwp_lift_base_step_nofork e tid E Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={∅}=> ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            BWP e' ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_base_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_atomic_base_step e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
        ∀ e' σ' es,
        ⌜base_step tid e σ κ e' σ' es⌝ -∗
        £ 1 -∗
          |={E1}[E2]▷=>
          state_interp (nt + length es) σ' κs ∗
          from_option Φ False (to_val e') ∗
          [∗ list] i ↦ e ∈ es,
            BWP e ∶ nt + i {{ fork_post }}
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%e' %σ' %es %Hstep".
    iApply ("H" with "[%]").
    naive_solver.
  Qed.
  Lemma bwp_lift_atomic_base_step_nofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ nt σ κ κs,
      state_interp nt σ (κ ++ κs) -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ e' σ' es,
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ 1 -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp nt σ' κs ∗
            from_option Φ False (to_val e')
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_base_step; first done. iIntros "%nt %σ %κ %κs Hσ".
    iMod ("H" with "Hσ") as "($ & H)".
    iIntros "!> %e' %σ' %es %Hstep H£".
    iMod ("H" with "[//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hσ & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_pure_base_step_nofork `{!Inhabited (state Λ)} e tid E1 E2 Φ :
    ( ∀ σ,
      base_reducible tid e σ
    ) →
    ( ∀ σ κ e' σ' es,
      base_step tid e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜base_step tid e σ κ e' σ es⌝ -∗
      £ 1 -∗
      BWP e' ∶ tid @ E1 {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply bwp_lift_pure_step_nofork; [eauto.. |].
    iMod "H" as "H".
    iIntros "!> !>".
    iMod "H".
    iIntros "!> %σ %e' %κ %es %Hstep H£".
    iApply ("H" with "[%] H£"); first eauto.
  Qed.

  Lemma bwp_lift_pure_det_base_step_nofork `{!Inhabited (state Λ)} e1 e2 tid E1 E2 Φ :
    ( ∀ σ1,
      base_reducible tid e1 σ1
    ) →
    ( ∀ σ1 κ e2' σ2 es,
      base_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
    ) →
    ( |={E1}[E2]▷=>
      £ 1 -∗
      BWP e2 ∶ tid @ E1 {{ Φ }}
    ) ⊢
    BWP e1 ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H".
    iApply bwp_lift_pure_det_step_nofork; [eauto.. |].
    iSteps.
  Qed.
End iris_G.
