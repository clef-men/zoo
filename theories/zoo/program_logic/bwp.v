From iris.base_logic Require Export
  lib.fancy_updates.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  tactics
  notations.
From zoo.program_logic Require Export
  state_interp.
From zoo Require Import
  options.

Parameter later_coefficient : nat.
Axiom later_coefficient_lb :
  2 ≤ later_coefficient.
#[global] Hint Resolve
  later_coefficient_lb
: core.

Parameter later_constant : nat.
Axiom later_constant_lb :
  2 ≤ later_constant.
#[global] Hint Resolve
  later_constant_lb
: core.

Definition later_function ns :=
  later_coefficient * ns + later_constant.
Lemma later_function_lb ns :
  later_constant ≤ later_function ns.
Proof.
  rewrite /later_function. lia.
Qed.
Lemma later_function_mono ns1 ns2 :
  ns1 ≤ ns2 →
  later_function ns1 ≤ later_function ns2.
Proof.
  intros.
  apply Nat.add_le_mono_r, Nat.mul_le_mono_l => //.
Qed.
Lemma later_function_0 :
  later_function 0 = later_constant.
Proof.
  rewrite /later_function. lia.
Qed.
#[global] Hint Resolve
  later_function_lb
  later_function_mono
: core.

Fixpoint later_sum ns n : nat :=
  match n with
  | 0 =>
      0
  | S n =>
      later_function ns + later_sum (S ns) n
  end.

Lemma later_sum_lb ns n :
  n * later_constant ≤ later_sum ns n.
Proof.
  move: ns. induction n as [| n IH] => ns.
  - lia.
  - apply Nat.add_le_mono; done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition bwp_pre (bwp : expr -d> thread_id -d> coPset -d> (val -d> iPropO Σ) -d> iPropO Σ)
  : expr -d> thread_id -d> coPset -d> (val -d> iPropO Σ) -d> iPropO Σ
  := (
    λ e tid E Φ,
      ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
      match to_val e with
      | Some v =>
          state_interp ns nt σ κs ∗
          Φ v
      | None =>
          |={E,∅}=>
          ⌜reducible tid e σ⌝ ∗
            ∀ κ κs' e' σ' es,
            ⌜κs = κ ++ κs'⌝ -∗
            ⌜prim_step tid e σ κ e' σ' es⌝ -∗
            £ (later_function ns) ={∅}=∗
              ▷ |={∅,E}=>
              state_interp (S ns) (nt + length es) σ' κs' ∗
              bwp e' tid E Φ ∗
              [∗ list] i ↦ e ∈ es,
                bwp e (nt + i) ⊤ fork_post
      end
  )%I.
  #[global] Arguments bwp_pre bwp e%_E tid E Φ%_I : rename.

  #[local] Instance bwp_pre_contractive :
    Contractive bwp_pre.
  Proof.
    rewrite /bwp_pre => n bwp1 bwp2 Hbwp e tid E Φ.
    repeat (apply Hbwp || f_contractive || f_equiv).
  Qed.

  #[local] Definition bwp_def
  : expr → thread_id → coPset → (val → iProp Σ) → iProp Σ
  :=
    fixpoint bwp_pre.
  #[global] Arguments bwp_def e%_E tid E Φ%_I : rename.
End zoo_G.

#[local] Definition bwp_aux : seal (@bwp_def).
  Proof. by eexists. Qed.
Definition bwp :=
  bwp_aux.(unseal).
#[global] Arguments bwp {_ _} e%_E tid E Φ%_I : rename.
#[local] Lemma bwp_unseal `{zoo_G : !ZooG Σ} :
  bwp = bwp_def.
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
)(at level 0,
  e at level 200,
  tid at level 200,
  E custom wp_mask at level 200,
  Φ at level 200,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BWP' e ∶ tid E {{ v , Q } }" := (
  bwp e%E tid E (λ v, Q%I)
)(at level 0,
  e at level 200,
  tid at level 200,
  E custom wp_mask at level 200,
  v at level 200 as pattern,
  Q at level 200,
  format "'[hv' BWP  '/  ' '[' e ']'  '/  ' ∶  tid  E '/' {{  '[' v ,  '/' Q ']'  '/' } } ']'"
) : bi_scope.

Implicit Types ns nt : nat.
Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types tid : thread_id.
Implicit Types σ : state.
Implicit Types κ κs : list observation.
Implicit Types prophs : list (val * val).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types P R : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Lemma bwp_unfold e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊣⊢
    bwp_pre bwp e tid E Φ.
  Proof.
    rewrite bwp_unseal.
    apply: (fixpoint_unfold bwp_pre).
  Qed.

  #[global] Instance bwp_ne e tid E n :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    move: e. induction (lt_wf n) as [n _ IH] => e Φ1 Φ2 HΦ.
    rewrite !bwp_unfold /bwp_pre.
    do 31 (f_contractive || f_equiv).
    apply IH; first done.
    f_equiv.
    eapply dist_le; last by apply SIdx.lt_le_incl.
    apply HΦ.
  Qed.
  #[global] Instance bwp_proper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (bwp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply equiv_dist => n.
    apply bwp_ne => v.
    apply equiv_dist. done.
  Qed.
  #[global] Instance bwp_contractive e tid E n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (bwp e tid E).
  Proof.
    intros He Φ1 Φ2 HΦ.
    rewrite !bwp_unfold /bwp_pre He.
    repeat (f_contractive || f_equiv).
  Qed.

  Lemma bwp_state_interp e tid E Φ :
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
        state_interp ns nt σ κs ∗
        BWP e ∶ tid @ E {{ Φ }}
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iEval (rewrite bwp_unfold).
    iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(Hinterp & H)".
    iApply (bwp_unfold with "H Hinterp").
  Qed.

  Lemma bwp_value_fupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_unfold.
    iSteps.
  Qed.
  Lemma bwp_value_fupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_value_fupd' => <- //.
  Qed.
  Lemma bwp_value' v tid E Φ :
    Φ v ⊢
    BWP of_val v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (bwp_value_fupd' with "HΦ").
  Qed.
  Lemma bwp_value e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_value' => <- //.
  Qed.

  Lemma bwp_value_mono v tid E Φ1 Φ2 :
    BWP of_val v ∶ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    BWP of_val v ∶ tid @ E {{ Φ2 }}.
  Proof.
    rewrite !bwp_unfold.
    iIntros "H HΦ %ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iSteps.
  Qed.

  Lemma bwp_strong_mono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    BWP e ∶ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    BWP e ∶ tid @ E2 {{ Φ2 }}.
  Proof.
    iIntros "%HE H HΦ".
    iLöb as "HLöb" forall (e).
    rewrite !bwp_unfold /bwp_pre.
    iIntros "%ns %nt %σ1 %κs Hinterp".
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hinterp") as "(Hinterp & HΦ1)".
      iSteps.
    - iModIntro.
      iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
      iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
      iStep. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep H£".
      iMod ("H" with "[//] [//] H£") as "H".
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
    rewrite {2}bwp_unfold.
    iIntros "H %ns %nt %σ %κs Hinterp".
    iMod "H" as "H".
    iRevert (ns nt σ κs) "Hinterp".
    iApply (bwp_unfold with "H").
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
    rewrite !bwp_unfold /bwp_pre.
    iIntros "H %ns %nt %σ %κs Hinterp".
    destruct (to_val e) as [v |] eqn:He.
    - iMod ("H" with "Hinterp") as ">($ & $)".
    - iModIntro.
      iMod ("H" with "Hinterp") as ">>(%Hreducible & H)".
      iStep. iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [//] H£") as "H".
      do 2 iModIntro.
      iMod "H" as "(Hinterp & H & $)".
      rewrite !bwp_unfold /bwp_pre.
      destruct (to_val e2) as [v2 |] eqn:He2.
      + iMod ("H" with "Hinterp") as "($ & >H)".
        iFrameSteps.
      + iMod ("H" with "Hinterp") as ">(%Hreducible2 & _)".
        destruct Hreducible2 as (κ2 & e3 & σ3 & es2 & Hstep2).
        edestruct atomic; [done | congruence].
  Qed.

  Lemma bwp_bind K `{!Context K} e tid E Φ :
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }} ⊢
    BWP K e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    rewrite bwp_unfold /bwp_pre.
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      iApply (bwp_state_interp with "H").
    - rewrite bwp_unfold /bwp_pre context_fill_not_val //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible1 & H)".
      iModIntro; iSplit; first eauto using reducible_context.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      destruct (context_fill_step_inv tid e σ1 κ e2 σ2 es1) as (e2' & -> & Hstep1'); [done.. |].
      iMod ("H" with "[//] [//] H£") as "H".
      iModIntro. iSteps.
  Qed.

  Lemma bwp_bind_inv K `{!Context K} e tid E Φ :
    BWP K e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ v, BWP K (of_val v) ∶ tid @ E {{ Φ }} }}.
  Proof.
    iIntros "H".
    iLöb as "IH" forall (e).
    destruct (to_val e) as [v |] eqn:He.
    - apply of_to_val in He as <-.
      iApply bwp_value'.
      iApply "H".
    - rewrite !bwp_unfold /bwp_pre context_fill_not_val He //.
      iIntros "%ns %nt %σ1 %κs Hinterp !>".
      iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
      iModIntro; iSplit; first eauto using reducible_context_inv.
      iIntros "%κ %κs' %e2 %σ2 %es1 -> %Hstep1 H£".
      iMod ("H" with "[//] [] H£") as "H".
      { eauto using context_fill_step. }
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
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma bwp_lift_step e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) ={∅}=∗
            ▷ |={∅, E}=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (S ns) -∗
                BWP e' ∶ tid @ E {{ Φ }} ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite bwp_unfold /bwp_pre => ->.
    iIntros "H %ns %nt %σ %κs Hinterp !>".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iStep 9 as (κ κs' e' σ' es Hstep) "H H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(Hinterp & H)".
    iMod (state_interp_mono with "Hinterp") as "Hinterp".
    iDestruct (state_interp_steps_lb_get with "Hinterp") as "#H⧖".
    iFrameSteps.
  Qed.
  Lemma bwp_lift_step_nofork e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) ={∅}=∗
            ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (S ns) -∗
              BWP e' ∶ tid @ E {{ Φ }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwp_lift_atomic_step e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E1}=∗
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) -∗
            |={E1}[E2]▷=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (S ns) -∗
                from_option Φ False (to_val e') ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod "Hclose" as "_".
    iMod ("H" with "[//] [//] H£") as "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_".
    iMod "H" as "($ & H)". iIntros "!> H⧖".
    iDestruct ("H" with "H⧖") as "(HΦ & $)".
    destruct (to_val e') eqn:He'; last by iExFalso.
    iApply (bwp_value with "HΦ").
    apply of_to_val. done.
  Qed.
  Lemma bwp_lift_atomic_step_nofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E1}=∗
        ⌜reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜prim_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (S ns) -∗
              from_option Φ False (to_val e')
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iFrameSteps.
  Qed.

  Lemma bwp_lift_pure_step_nofork e tid ns E1 E2 Φ :
    ( ∀ σ,
      reducible tid e σ
    ) →
    ( ∀ σ κ e' σ' es,
      prim_step tid e σ κ e' σ' es →
        κ = [] ∧
        σ' = σ ∧
        es = []
    ) →
    ⧖ ns -∗
    ( |={E1}[E2]▷=>
      ∀ σ e' κ es,
      ⌜prim_step tid e σ κ e' σ es⌝ -∗
      ⧖ (S ns) -∗
      £ (later_function ns) -∗
      BWP e' ∶ tid @ E1 {{ Φ }}
    ) -∗
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H⧖ H".
    iApply bwp_lift_step_nofork.
    { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
    iIntros "%ns' %nt %σ %κs Hinterp".
    iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep H£ !> !>".
    edestruct Hpure as (? & ? & ?); first done. subst.
    iDestruct (state_interp_steps_lb_valid with "Hinterp H⧖") as %?.
    iDestruct (lc_weaken (later_function ns) with "H£") as "H£"; first auto.
    iFrameStep 2.
    iMod "H".
    iSteps.
  Qed.

  Lemma bwp_lift_pure_det_step_nofork e1 e2 tid ns E1 E2 Φ :
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
    ⧖ ns -∗
    ( |={E1}[E2]▷=>
      ⧖ (S ns) -∗
      £ (later_function ns) -∗
      BWP e2 ∶ tid @ E1 {{ Φ }}
    ) -∗
    BWP e1 ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%Hsafe %Hpure H⧖ H".
    iApply (bwp_lift_pure_step_nofork with "H⧖"); [done | naive_solver |].
    iApply (step_fupd_wand with "H"). iIntros "H %σ1 %e2' %κ %es %Hstep H£".
    apply Hpure in Hstep as (-> & _ & -> & ->).
    iSteps.
  Qed.

  Lemma bwp_pure_step ϕ n e1 e2 ns tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ⧖ ns -∗
    ▷^n (
      ⧖ (ns + n) -∗
      £ (later_sum ns n) -∗
      BWP e2 ∶ tid @ E {{ Φ }}
    ) -∗
    BWP e1 ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hϕ H⧖ H".
    specialize (Hexec Hϕ).
    iInduction Hexec as [e | n e1 e2 e3 (Hsafe & Hpure)] "IH" forall (ns).
    - iMod lc_zero as "H£".
      iSteps.
    - iApply (bwp_lift_pure_det_step_nofork with "H⧖").
      { eauto using reducible_no_obs_reducible. }
      { eauto. }
      do 3 iModIntro.
      rewrite lc_split. iSteps.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  #[local] Hint Resolve
    base_reducible_reducible
    base_reducible_prim_step
  : core.

  Lemma bwp_lift_base_step e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) ={∅}=∗
            ▷ |={∅, E}=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (S ns) -∗
                BWP e' ∶ tid @ E {{ Φ }} ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwp_lift_base_step_nofork e tid E Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E, ∅}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) ={∅}=∗
            ▷ |={∅, E}=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ ns -∗
              BWP e' ∶ tid @ E {{ Φ }}
            )
    ) ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_base_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.

  Lemma bwp_lift_atomic_base_step e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) -∗
            |={E1}[E2]▷=>
            state_interp ns (nt + length es) σ' κs' ∗
            ( ⧖ (S ns) -∗
                from_option Φ False (to_val e') ∗
                [∗ list] i ↦ e ∈ es,
                  BWP e ∶ nt + i {{ fork_post }}
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "(%Hreducible & H)".
    iModIntro. iSplit; first iSteps. iIntros "%κ %κs' %e' %σ' %es -> %Hstep".
    iApply ("H" with "[//] [%]"); first auto.
  Qed.
  Lemma bwp_lift_atomic_base_step_nofork e tid E1 E2 Φ :
    to_val e = None →
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs -∗
        |={E1}=>
        ⌜base_reducible tid e σ⌝ ∗
          ∀ κ κs' e' σ' es,
          ⌜κs = κ ++ κs'⌝ -∗
          ⌜base_step tid e σ κ e' σ' es⌝ -∗
          £ (later_function ns) -∗
            |={E1}[E2]▷=>
            ⌜es = []⌝ ∗
            state_interp ns nt σ' κs' ∗
            ( ⧖ (S ns) -∗
              from_option Φ False (to_val e')
            )
    ) ⊢
    BWP e ∶ tid @ E1 {{ Φ }}.
  Proof.
    iIntros "%He H".
    iApply bwp_lift_atomic_base_step; first done. iIntros "%ns %nt %σ %κs Hinterp".
    iMod ("H" with "Hinterp") as "($ & H)".
    iIntros "!> %κ %κs' %e' %σ' %es -> %Hstep H£".
    iMod ("H" with "[//] [//] H£") as "H".
    do 2 iModIntro.
    iMod "H" as "(-> & Hinterp & H)".
    rewrite Nat.add_0_r. iSteps.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma bwp_match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP e ∶ tid @ E {{ Φ }} -∗
    BWP Match #l x_fb e_fb brs ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He >#Hl H".
    iApply bwp_lift_base_step_nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp_headers_at_valid with "Hinterp Hl") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e_ %σ_ %es -> %Hstep _ !>".
    invert_base_step.
    iSteps.
  Qed.
  Lemma bwp_match_context K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ BWP K e ∶ tid @ E {{ Φ }} -∗
    BWP K (Match #l x_fb e_fb brs) ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He Hl H".
    iApply bwp_bind.
    iApply (bwp_match with "Hl"); first done.
    iApply (bwp_bind_inv with "H").
  Qed.

  Lemma bwp_resolve_strong e pid v tid E Φ :
    to_val e = None →
    ( BWP e ∶ tid @ E {{ res,
        ∃ prophs,
        prophet_model pid prophs ∗
          ∀ prophs',
          ⌜prophs = (res, v) :: prophs'⌝ -∗
          prophet_model pid prophs' -∗
          Φ res
      }}
    ) ⊢
    BWP Resolve e #pid v ∶ tid @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "%He H".
    rewrite !bwp_unfold /bwp_pre He.
    iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iMod ("H" with "Hinterp") as ">(%Hreducible & H)".
    iSplitR. { iPureIntro. apply reducible_resolve => //. }
    iIntros "!> %κ %κs' %e2 %σ2 %es -> %Hstep H£".
    destruct (to_val e2) as [v2 |] eqn:Heq.
    - destruct κ as [| (pid' & (w' & v')) κ _] using rev_ind.
      + exfalso. apply prim_step_resolve_inv_val in Hstep. 2: done.
        invert_base_step.
        destruct κ => //.
      + apply prim_step_resolve_inv_val in Hstep. 2: done.
        invert_base_step. simplify_list_eq.
        apply base_step_prim_step in H as Hstep.
        iMod ("H" with "[%] [%] H£") as "H". 1-2: done.
        do 2 iModIntro.
        iMod "H" as "(Hinterp & H & $)".
        iDestruct (bwp_unfold with "H") as "H".
        iMod ("H" with "Hinterp") as "(Hinterp & %prophs & Hpid' & H)".
        iMod (state_interp_prophet_resolve with "Hinterp Hpid'") as "(%prophs' & -> & $ & Hpid')".
        iApply bwp_unfold.
        iSteps.
    - apply prim_step_resolve_inv_non_val in Hstep as (e' & -> & He' & Hstep). 2: done.
      iMod ("H" with "[%] [%] H£") as "H". 1-2: done.
      do 2 iModIntro.
      iMod "H" as "($ & H & $)".
      iSteps.
  Qed.
  Lemma bwp_resolve e pid v prophs tid E Φ :
    to_val e = None →
    prophet_model pid prophs -∗
    BWP e ∶ tid @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet_model pid prophs' -∗
      Φ res
    }} -∗
    BWP Resolve e #pid v ∶ tid @ E {{ Φ }}.
  Proof.
    iIntros "%He Hpid H".
    iApply bwp_resolve_strong. 1: done.
    iApply (bwp_wand with "H").
    iSteps.
  Qed.
End zoo_G.
