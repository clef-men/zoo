From zebre Require Import
  prelude.
From zebre.iris.bi Require Import
  big_op.
From zebre.iris Require Import
  diaframe.
From zebre.iris.program_logic Require Export
  wp.
From zebre Require Import
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

  #[local] Lemma wp_step e1 σ1 e2 σ2 κ κs es ϕ Φ :
    prim_step e1 σ1 κ e2 σ2 es ϕ →
    ϕ →
    state_interp σ1 (κ ++ κs) -∗
    £ 1 -∗
    WP e1 @ ⊤ {{ Φ }} -∗
      |={⊤}[∅]▷=>
      state_interp σ2 κs ∗
      WP e2 @ ⊤ {{ Φ }} ∗
      wps es (replicate (length es) fork_post).
  Proof.
    iIntros "%Hstep %Hϕ Hσ H£ H".
    rewrite {1}wp_unfold /wp_pre (val_stuck e1 σ1 κ e2 σ2 es ϕ) //.
    iMod ("H" with "Hσ") as "(_ & H)".
    iMod ("H" with "[//] [//] H£") as "H".
    iModIntro. iSteps. rewrite /wps big_sepL2_replicate_r //.
  Qed.

  #[local] Lemma wps_step es1 σ1 es2 σ2 κ κs ϕ Φs :
    step (es1, σ1) κ (es2, σ2) ϕ →
    ϕ →
    state_interp σ1 (κ ++ κs) -∗
    £ 1 -∗
    wps es1 Φs -∗
      |={⊤}[∅]▷=>
      ∃ n_forked,
      state_interp σ2 κs ∗
      wps es2 (Φs ++ replicate n_forked fork_post).
  Proof.
    iIntros "%Hstep %Hϕ Hσ H£ H".
    destruct Hstep as [e1 σ1' e2 σ2' es es1' es2' Hstep]; simplify_eq/=.
    iDestruct (big_sepL2_app_inv_l with "H") as (Φs1 Φs2 ->) "(Hes1' & H)".
    iDestruct (big_sepL2_cons_inv_l with "H") as (Φ Φs3 ->) "(He1 & Hes2')".
    iMod (wp_step with "Hσ H£ He1") as "H"; [done.. |].
    iExists _. rewrite -(assoc (++)) -app_comm_cons. iFrame. iSteps.
  Qed.

  #[local] Lemma wps_steps n es1 σ1 es2 σ2 κs1 κs2 ϕs Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) ϕs →
    Forall id ϕs →
    state_interp σ1 (κs1 ++ κs2) -∗
    £ n -∗
    wps es1 Φs -∗
      |={⊤,∅}=> |={∅}▷=>^n |={∅,⊤}=>
      ∃ n_forked,
      state_interp σ2 κs2 ∗
      wps es2 (Φs ++ replicate n_forked fork_post).
  Proof.
    iInduction n as [| n] "IH" forall (es1 σ1 κs1 κs2 ϕs Φs) => /=.
    all: iIntros "%Hsteps %Hϕs Hσ H£s H".
    - invert Hsteps.
      iExists 0. rewrite right_id. iSteps.
    - invert Hsteps as [| ? ? (es1' & σ1') ? κ κs1' ϕ ϕs' Hstep Hsteps'].
      apply Forall_cons in Hϕs as (Hϕ & Hϕs').
      rewrite -(assoc (++)).
      iDestruct "H£s" as "(H£ & H£s)".
      iMod (wps_step with "Hσ H£ H") as "H"; [done.. |].
      do 3 iModIntro.
      iApply (fupd_trans _ ⊤).
      iMod "H" as "(%n_forked & Hσ & H)".
      iModIntro.
      iMod ("IH" with "[//] [//] Hσ H£s H") as "H"; [done.. |].
      iModIntro.
      iApply (step_fupdN_wand with "H"). iIntros ">H".
      iDestruct "H" as "(%n_forked' & Hσ & H)".
      rewrite -(assoc app) -replicate_add. iSteps.
  Qed.

  #[local] Lemma wp_not_stuck e σ κs Φ :
    state_interp σ κs -∗
    WP e {{ Φ }} -∗
      |={⊤, ∅}=>
      ⌜not_stuck e σ⌝.
  Proof.
    iIntros "Hσ H".
    rewrite wp_unfold /wp_pre /not_stuck.
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq ∅); first done.
      iSteps.
    - iSpecialize ("H" $! σ [] κs with "Hσ").
      iMod "H" as "(%Hreducible & _)".
      iSteps.
  Qed.

  #[local] Lemma wps_progress n es1 σ1 e2 es2 σ2 κs1 κs2 ϕs Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) ϕs →
    Forall id ϕs →
    e2 ∈ es2 →
    state_interp σ1 (κs1 ++ κs2) -∗
    £ n -∗
    wps es1 Φs -∗
      |={⊤, ∅}=> |={∅}▷=>^n |={∅}=>
      ⌜not_stuck e2 σ2⌝.
  Proof.
    iIntros (Hsteps Hϕs (i & Hes2_lookup)%elem_of_list_lookup) "Hσ H£s He".
    iMod (wps_steps with "Hσ H£s He") as "H"; [done.. |].
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "(%n_forked & Hσ & H)".
    iDestruct (big_sepL2_lookup_Some_l with "H") as %(Φ & Hposts_lookup); first done.
    iDestruct (big_sepL2_lookup with "H") as "H"; [done.. |].
    iApply (wp_not_stuck with "Hσ H").
  Qed.
End iris_G.

Lemma wp_progress Λ Σ `{inv_Gpre : !invGpreS Σ} n es1 σ1 e2 es2 σ2 κs ϕs :
  ( ∀ `{inv_G : !invGS Σ},
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φs,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp σ1 κs ∗
      wps es1 Φs
  ) →
  nsteps n (es1, σ1) κs (es2, σ2) ϕs →
  Forall id ϕs →
  e2 ∈ es2 →
  not_stuck e2 σ2.
Proof.
  intros H Hsteps Hϕs He2.
  eapply uPred.pure_soundness, (step_fupdN_soundness_lc _ n n).
  iIntros "%Hinv_G H£s".
  iMod H as "(%state_interp & %fork_post & %Φs & Hσ & H)".
  iMod (wps_progress (iris_G := Build_IrisG state_interp fork_post) with "[Hσ] H£s H") as "H"; [done.. | |].
  { erewrite app_nil_r. done. }
  destruct n.
  - iMod "H". iSteps.
  - iApply step_fupdN_S_fupd. iSteps.
Qed.

Definition adequate {Λ} (e : expr Λ) σ :=
  ∀ n κs e' es σ' ϕs,
  nsteps n ([e], σ) κs (es, σ') ϕs →
  Forall id ϕs →
  e' ∈ es →
  not_stuck e' σ'.

Lemma wp_adequacy Λ Σ `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ state_interp fork_post Φ,
      let iris_G : IrisG Λ Σ := Build_IrisG state_interp fork_post in
      state_interp σ κs ∗
      WP e {{ Φ }}
  ) →
  adequate e σ.
Proof.
  intros H n κs e' es σ' ϕs.
  apply: wp_progress => inv_G.
  iMod H as "(%state_interp & %fork_post & %Φ & Hσ & H)".
  iExists state_interp, fork_post, [Φ]. rewrite /wps /=. iSteps.
Qed.
