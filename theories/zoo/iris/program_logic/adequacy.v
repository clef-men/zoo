From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Export
  wp.
From zoo Require Import
  options.

Section iris_G.
  Context `{iris_G : !IrisG Λ Σ}.

  Implicit Types e : expr Λ.
  Implicit Types es : list (expr Λ).
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types Φs : list (val Λ → iProp Σ).

  Definition bwps nt es Φs : iProp Σ :=
    [∗ list] i ↦ e; Φ ∈ es; Φs,
      BWP e ∶ nt + i {{ Φ }}.

  #[local] Lemma bwp_step tid e1 σ1 e2 σ2 κ κs es nt Φ :
    prim_step tid e1 σ1 κ e2 σ2 es →
    state_interp nt σ1 (κ ++ κs) -∗
    £ 1 -∗
    BWP e1 ∶ tid {{ Φ }} -∗
      |={⊤}[∅]▷=>
      state_interp (nt + length es) σ2 κs ∗
      BWP e2 ∶ tid {{ Φ }} ∗
      bwps nt es (replicate (length es) fork_post).
  Proof.
    iIntros "%Hstep Hσ H£ H".
    rewrite {1}bwp_unfold /bwp_pre (val_stuck tid e1 σ1 κ e2 σ2 es) //.
    iMod ("H" with "Hσ") as "(_ & >H)".
    iMod ("H" with "[//] [//] H£") as "H".
    iModIntro.
    iSteps. rewrite /bwps big_sepL2_replicate_r //.
  Qed.
  #[local] Lemma bwps_step es1 σ1 es2 σ2 κ κs Φs :
    step (es1, σ1) κ (es2, σ2) →
    state_interp (length es1) σ1 (κ ++ κs) -∗
    £ 1 -∗
    bwps 0 es1 Φs -∗
      |={⊤}[∅]▷=>
      state_interp (length es2) σ2 κs ∗
      bwps 0 es2 (Φs ++ replicate (length es2 - length es1) fork_post).
  Proof.
    iIntros ((i & e1 & e2 & σ2' & es & Hstep & Hes1_lookup & [= -> <-])) "Hσ H£ H".
    iDestruct (big_sepL2_insert_acc_l with "H") as "(%Φ & %HΦs_lookup & He1 & H)"; first done.
    iMod (bwp_step with "Hσ H£ He1") as "He1"; first done.
    do 2 iModIntro.
    iMod "He1" as "(Hσ & He2 & Hes)".
    iDestruct ("H" with "He2") as "H".
    rewrite length_app length_insert Nat.add_sub'.
    rewrite (list_insert_id Φs) // big_sepL2_app length_insert.
    iSteps.
  Qed.
  #[local] Lemma bwps_steps n es1 σ1 es2 σ2 κs1 κs2 Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    state_interp (length es1) σ1 (κs1 ++ κs2) -∗
    £ n -∗
    bwps 0 es1 Φs -∗
      |={⊤,∅}=> |={∅}▷=>^n |={∅,⊤}=>
      state_interp (length es2) σ2 κs2 ∗
      bwps 0 es2 (Φs ++ replicate (length es2 - length es1) fork_post).
  Proof.
    iInduction n as [| n] "IH" forall (es1 σ1 κs1 κs2 Φs) => /=.
    all: iIntros "%Hsteps Hσ H£s H".
    - invert Hsteps.
      rewrite Nat.sub_diag right_id. iSteps.
    - invert Hsteps as [| ? ? (es1' & σ1') ? κ κs1' Hstep Hsteps'].
      rewrite -(assoc (++)).
      iDestruct "H£s" as "(H£ & H£s)".
      iMod (bwps_step with "Hσ H£ H") as "H"; [done.. |].
      do 3 iModIntro.
      iApply (fupd_trans _ ⊤).
      iMod "H" as "(Hσ & H)".
      iModIntro.
      iMod ("IH" with "[//] Hσ H£s H") as "H".
      iModIntro.
      iApply (step_fupdN_wand with "H"). iIntros ">H".
      iDestruct "H" as "(Hσ & H)".
      rewrite -assoc -replicate_add.
      assert (length es1' - length es1 + (length es2 - length es1') = length es2 - length es1) as ->.
      { apply step_length in Hstep.
        apply nsteps_length in Hsteps'.
        naive_solver lia.
      }
      iSteps.
  Qed.

  #[local] Lemma bwp_not_stuck e tid nt σ κs Φ :
    state_interp nt σ κs -∗
    BWP e ∶ tid {{ Φ }} -∗
      |={⊤, ∅}=>
      ⌜not_stuck tid e σ⌝.
  Proof.
    iIntros "Hσ H".
    rewrite bwp_unfold /bwp_pre /not_stuck.
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq ∅); first done.
      iSteps.
    - iMod ("H" with "Hσ") as ">(%Hreducible & _)".
      iSteps.
  Qed.

  #[local] Lemma bwps_progress n es1 σ1 tid e2 es2 σ2 κs1 κs2 Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    es2 !! tid = Some e2 →
    state_interp (length es1) σ1 (κs1 ++ κs2) -∗
    £ n -∗
    bwps 0 es1 Φs -∗
      |={⊤, ∅}=> |={∅}▷=>^n |={∅}=>
      ⌜not_stuck tid e2 σ2⌝.
  Proof.
    iIntros (Hsteps Hes2_lookup) "Hσ H£s He".
    iMod (bwps_steps with "Hσ H£s He") as "H"; [done.. |].
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "(Hσ & H)".
    iDestruct (big_sepL2_lookup_Some_l with "H") as %(Φ & Hposts_lookup); first done.
    iDestruct (big_sepL2_lookup with "H") as "H"; [done.. |].
    iApply (bwp_not_stuck with "Hσ H").
  Qed.
End iris_G.

Lemma bwp_progress Λ `{inv_Gpre : !invGpreS Σ} n es1 σ1 es2 σ2 κs :
  ( ∀ `{inv_G : !invGS Σ},
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φs,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp (length es1) σ1 κs ∗
      bwps 0 es1 Φs
  ) →
  nsteps n (es1, σ1) κs (es2, σ2) →
  Foralli (λ tid e2, not_stuck tid e2 σ2) es2.
Proof.
  intros H Hsteps.
  apply Foralli_lookup => tid e2 Hlookup.
  eapply uPred.pure_soundness, (step_fupdN_soundness_lc _ n n).
  iIntros "%Hinv_G H£s".
  iMod H as "(%state_interp & %fork_post & %Φs & Hσ & H)".
  iMod (bwps_progress (iris_G := Build_IrisG state_interp fork_post) with "[Hσ] H£s H") as "H"; [done.. | |].
  { erewrite app_nil_r => //. }
  destruct n.
  - iMod "H". iSteps.
  - iApply step_fupdN_S_fupd. iSteps.
Qed.

Lemma bwp_adequacy Λ `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φ,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp 1 σ κs ∗
      BWP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H (es, σ') (n & κs & Hsteps)%silent_steps_nsteps.
  move: Hsteps. apply: bwp_progress => inv_G.
  iMod H as "(%state_interp & %fork_post & %Φ & Hσ & H)".
  iExists state_interp, fork_post, [Φ].
  rewrite /bwps /=. iSteps.
Qed.
Lemma wp_adequacy Λ `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φ,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp 1 σ κs ∗
      WP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H.
  apply: bwp_adequacy => inv_G κs.
  iMod H as "(%state_interp & %fork_post & %Φ & Hσ & Hwp)".
  iExists state_interp, fork_post, Φ. iFrame.
  iApply (wp_bwp with "Hwp").
Qed.
