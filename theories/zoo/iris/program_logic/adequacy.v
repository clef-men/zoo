From zoo Require Import
  prelude.
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

  Definition wps es Φs : iProp Σ :=
    [∗ list] e; Φ ∈ es; Φs,
      WP e @ ⊤ {{ Φ }}.

  #[local] Lemma wp_step e1 σ1 e2 σ2 κ κs es nt Φ :
    prim_step e1 σ1 κ e2 σ2 es →
    state_interp nt σ1 (κ ++ κs) -∗
    £ 1 -∗
    WP e1 @ ⊤ {{ Φ }} -∗
      |={⊤}[∅]▷=>
      state_interp (nt + length es) σ2 κs ∗
      WP e2 @ ⊤ {{ Φ }} ∗
      wps es (replicate (length es) fork_post).
  Proof.
    iIntros "%Hstep Hσ H£ H".
    rewrite {1}wp_unfold /wp_pre (val_stuck e1 σ1 κ e2 σ2 es) //.
    iMod ("H" with "Hσ") as "(_ & H)".
    iMod ("H" with "[//] H£") as "H".
    iModIntro. iSteps. rewrite /wps big_sepL2_replicate_r //.
  Qed.
  #[local] Lemma wps_step es1 σ1 es2 σ2 κ κs nt Φs :
    step (es1, σ1) κ (es2, σ2) →
    state_interp nt σ1 (κ ++ κs) -∗
    £ 1 -∗
    wps es1 Φs -∗
      |={⊤}[∅]▷=>
      ∃ n_fork,
      state_interp (nt + n_fork) σ2 κs ∗
      wps es2 (Φs ++ replicate n_fork fork_post).
  Proof.
    iIntros ((i & e1 & e2 & σ2' & es & Hstep & Hes1_lookup & [= -> <-])) "Hσ H£ H".
    iDestruct (big_sepL2_insert_acc_l with "H") as "(%Φ & %HΦs_lookup & He1 & H)"; first done.
    iMod (wp_step with "Hσ H£ He1") as "He1"; first done.
    do 2 iModIntro.
    iMod "He1" as "(Hσ & He2 & Hes)".
    iDestruct ("H" with "He2") as "H".
    rewrite (list_insert_id Φs) // big_sepL2_app.
    iSteps.
  Qed.
  #[local] Lemma wps_steps n es1 σ1 es2 σ2 κs1 κs2 nt Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    state_interp nt σ1 (κs1 ++ κs2) -∗
    £ n -∗
    wps es1 Φs -∗
      |={⊤,∅}=> |={∅}▷=>^n |={∅,⊤}=>
      ∃ n_fork,
      state_interp (nt + n_fork) σ2 κs2 ∗
      wps es2 (Φs ++ replicate n_fork fork_post).
  Proof.
    iInduction n as [| n] "IH" forall (es1 σ1 κs1 κs2 nt Φs) => /=.
    all: iIntros "%Hsteps Hσ H£s H".
    - invert Hsteps.
      iExists 0. rewrite Nat.add_0_r right_id. iSteps.
    - invert Hsteps as [| ? ? (es1' & σ1') ? κ κs1' Hstep Hsteps'].
      rewrite -(assoc (++)).
      iDestruct "H£s" as "(H£ & H£s)".
      iMod (wps_step with "Hσ H£ H") as "H"; [done.. |].
      do 3 iModIntro.
      iApply (fupd_trans _ ⊤).
      iMod "H" as "(%n_fork & Hσ & H)".
      iModIntro.
      iMod ("IH" with "[//] Hσ H£s H") as "H"; [done.. |].
      iModIntro.
      iApply (step_fupdN_wand with "H"). iIntros ">H".
      iDestruct "H" as "(%n_fork' & Hσ & H)".
      iEval (rewrite -assoc) in "Hσ". rewrite -assoc -replicate_add. iSteps.
  Qed.

  #[local] Lemma wp_not_stuck e nt σ κs Φ :
    state_interp nt σ κs -∗
    WP e {{ Φ }} -∗
      |={⊤, ∅}=>
      ⌜not_stuck e σ⌝.
  Proof.
    iIntros "Hσ H".
    rewrite wp_unfold /wp_pre /not_stuck.
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq ∅); first done.
      iSteps.
    - iSpecialize ("H" $! _ _ [] with "Hσ").
      iMod "H" as "(%Hreducible & _)".
      iSteps.
  Qed.

  #[local] Lemma wps_progress n es1 σ1 e2 es2 σ2 κs1 κs2 nt Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    e2 ∈ es2 →
    state_interp nt σ1 (κs1 ++ κs2) -∗
    £ n -∗
    wps es1 Φs -∗
      |={⊤, ∅}=> |={∅}▷=>^n |={∅}=>
      ⌜not_stuck e2 σ2⌝.
  Proof.
    iIntros (Hsteps (i & Hes2_lookup)%elem_of_list_lookup) "Hσ H£s He".
    iMod (wps_steps with "Hσ H£s He") as "H"; [done.. |].
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "(%n_fork & Hσ & H)".
    iDestruct (big_sepL2_lookup_Some_l with "H") as %(Φ & Hposts_lookup); first done.
    iDestruct (big_sepL2_lookup with "H") as "H"; [done.. |].
    iApply (wp_not_stuck with "Hσ H").
  Qed.
End iris_G.

Lemma wp_progress Λ Σ `{inv_Gpre : !invGpreS Σ} n es1 σ1 es2 σ2 κs :
  ( ∀ `{inv_G : !invGS Σ},
    ⊢ |={⊤}=>
      ∃ state_interp fork_post nt Φs,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp nt σ1 κs ∗
      wps es1 Φs
  ) →
  nsteps n (es1, σ1) κs (es2, σ2) →
  Forall (λ e2, not_stuck e2 σ2) es2.
Proof.
  intros H Hsteps.
  apply Forall_forall => e2 He2.
  eapply uPred.pure_soundness, (step_fupdN_soundness_lc _ n n).
  iIntros "%Hinv_G H£s".
  iMod H as "(%state_interp & %fork_post & %nt & %Φs & Hσ & H)".
  iMod (wps_progress (iris_G := Build_IrisG state_interp fork_post) with "[Hσ] H£s H") as "H"; [done.. | |].
  { erewrite app_nil_r => //. }
  destruct n.
  - iMod "H". iSteps.
  - iApply step_fupdN_S_fupd. iSteps.
Qed.

Lemma wp_adequacy Λ Σ `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ state_interp fork_post nt Φ,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp nt σ κs ∗
      WP e {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H (es, σ') (n & κs & Hsteps)%silent_steps_nsteps.
  move: Hsteps. apply: wp_progress => inv_G.
  iMod H as "(%state_interp & %fork_post & %nt & %Φ & Hσ & H)".
  iExists state_interp, fork_post, nt, [Φ]. rewrite /wps /=. iSteps.
Qed.
