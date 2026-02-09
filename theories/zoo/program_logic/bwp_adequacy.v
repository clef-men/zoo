From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris Require Import
diaframe.
From zoo.program_logic Require Export
  bwp.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types es : list expr.

#[local] Fixpoint later_sum ns n : nat :=
  match n with
  | 0 =>
      0
  | S n =>
      later_function ns + later_sum (S ns) n
  end.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.
  Implicit Types Φs : list (val → iProp Σ).

  Definition bwps nt es Φs : iProp Σ :=
    [∗ list] i ↦ e; Φ ∈ es; Φs,
      BWP e ∶ nt + i {{ Φ }}.

  #[local] Lemma bwp_step tid e1 σ1 e2 σ2 κ κs es ns nt Φ :
    prim_step tid e1 σ1 κ e2 σ2 es →
    state_interp ns nt σ1 (κ ++ κs) -∗
    £ (later_function ns) -∗
    BWP e1 ∶ tid {{ Φ }} -∗
      |={⊤}[∅]▷=>
      state_interp (S ns) (nt + length es) σ2 κs ∗
      BWP e2 ∶ tid {{ Φ }} ∗
      bwps nt es (replicate (length es) fork_post).
  Proof.
    iIntros "%Hstep Hinterp H£ H".
    rewrite {1}bwp_unfold /bwp_pre (prim_step_not_val tid e1 σ1 κ e2 σ2 es) //.
    iMod ("H" with "Hinterp") as "(_ & >H)".
    iMod ("H" with "[//] [//] H£") as "H".
    iModIntro.
    iSteps. rewrite /bwps big_sepL2_replicate_r //.
  Qed.
  #[local] Lemma bwps_step es1 σ1 es2 σ2 κ κs ns Φs :
    step (es1, σ1) κ (es2, σ2) →
    state_interp ns (length es1) σ1 (κ ++ κs) -∗
    £ (later_function ns) -∗
    bwps 0 es1 Φs -∗
      |={⊤}[∅]▷=>
      state_interp (S ns) (length es2) σ2 κs ∗
      bwps 0 es2 (Φs ++ replicate (length es2 - length es1) fork_post).
  Proof.
    iIntros ((i & e1 & e2 & σ2' & es & Hstep & Hes1_lookup & [= -> <-])) "Hinterp H£ H".
    iDestruct (big_sepL2_insert_acc_l with "H") as "(%Φ & %HΦs_lookup & He1 & H)"; first done.
    iMod (bwp_step with "Hinterp H£ He1") as "He1"; first done.
    do 2 iModIntro.
    iMod "He1" as "(Hinterp & He2 & Hes)".
    iDestruct ("H" with "He2") as "H".
    simpl_length. rewrite Nat.add_sub' (list_insert_id Φs) // big_sepL2_app. simpl_length.
    iSteps.
  Qed.
  #[local] Lemma bwps_steps n es1 σ1 es2 σ2 κs1 κs2 ns Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    state_interp ns (length es1) σ1 (κs1 ++ κs2) -∗
    £ (later_sum ns n) -∗
    bwps 0 es1 Φs -∗
      |={⊤,∅}=> |={∅}▷=>^n |={∅,⊤}=>
      state_interp (ns + n) (length es2) σ2 κs2 ∗
      bwps 0 es2 (Φs ++ replicate (length es2 - length es1) fork_post).
  Proof.
    iInduction n as [| n] "IH" forall (es1 σ1 κs1 κs2 ns Φs) => /=.
    all: iIntros "%Hsteps Hinterp H£s H".
    - invert Hsteps.
      rewrite Nat.add_0_r Nat.sub_diag app_nil_r.
      iFrameSteps.
    - invert Hsteps as [| ? ? (es1' & σ1') ? κ κs1' Hstep Hsteps'].
      rewrite -(assoc (++)).
      iDestruct "H£s" as "(H£ & H£s)".
      iMod (bwps_step with "Hinterp H£ H") as "H"; [done.. |].
      do 3 iModIntro.
      iApply (fupd_trans _ ⊤).
      iMod "H" as "(Hinterp & H)".
      iModIntro.
      iMod ("IH" with "[//] Hinterp H£s H") as "H".
      iModIntro.
      iApply (step_fupdN_wand with "H"). iIntros ">H".
      iDestruct "H" as "(Hinterp & H)".
      rewrite -assoc -replicate_add Nat.add_succ_comm.
      assert (length es1' - length es1 + (length es2 - length es1') = length es2 - length es1) as ->.
      { apply step_length in Hstep.
        apply nsteps_length in Hsteps'.
        naive_solver lia.
      }
      iFrameSteps.
  Qed.

  #[local] Lemma bwp_not_stuck e tid ns nt σ κs Φ :
    state_interp ns nt σ κs -∗
    BWP e ∶ tid {{ Φ }} -∗
      |={⊤, ∅}=>
      ⌜not_stuck tid e σ⌝.
  Proof.
    iIntros "Hinterp H".
    rewrite bwp_unfold /bwp_pre /not_stuck.
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq ∅); first done.
      iSteps.
    - iMod ("H" with "Hinterp") as ">(%Hreducible & _)".
      iSteps.
  Qed.

  #[local] Lemma bwps_progress n es1 σ1 tid e2 es2 σ2 κs1 κs2 ns Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    es2 !! tid = Some e2 →
    state_interp ns (length es1) σ1 (κs1 ++ κs2) -∗
    £ (later_sum ns n) -∗
    bwps 0 es1 Φs -∗
      |={⊤, ∅}=> |={∅}▷=>^n |={∅}=>
      ⌜not_stuck tid e2 σ2⌝.
  Proof.
    iIntros (Hsteps Hes2_lookup) "Hinterp H£s He".
    iMod (bwps_steps with "Hinterp H£s He") as "H"; [done.. |].
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "(Hinterp & H)".
    iDestruct (big_sepL2_lookup_Some_l with "H") as %(Φ & Hposts_lookup); first done.
    iDestruct (big_sepL2_lookup with "H") as "H"; [done.. |].
    iApply (bwp_not_stuck with "Hinterp H").
  Qed.
End zoo_G.

Lemma bwp_progress `{inv_Gpre : !invGpreS Σ} n es1 σ1 es2 σ2 κs :
  ( ∀ `{inv_G : !invGS Σ},
    ⊢ |={⊤}=>
      ∃ (zoo_G : ZooG Σ) Φs,
      ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
      state_interp 0 (length es1) σ1 κs ∗
      bwps 0 es1 Φs
  ) →
  nsteps n (es1, σ1) κs (es2, σ2) →
  Foralli (λ tid e2, not_stuck tid e2 σ2) es2.
Proof.
  intros H Hsteps.
  apply Foralli_lookup => tid e2 Hlookup.
  eapply uPred.pure_soundness, (step_fupdN_soundness_lc _ n (later_sum 0 n)).
  iIntros "%Hinv_G H£s".
  iMod H as "(%zoo_G & %Φs & <- & Hinterp & H)".
  iMod (bwps_progress with "[Hinterp] H£s H") as "H". 1,2: done.
  { erewrite app_nil_r => //. }
  destruct n.
  - iMod "H". iSteps.
  - iApply step_fupdN_S_fupd. iSteps.
Qed.

Lemma bwp_adequacy' `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv_G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ (zoo_G : ZooG Σ) Φ,
      ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
      state_interp 0 1 σ κs ∗
      BWP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H (es, σ') (n & κs & Hsteps)%silent_steps_nsteps.
  move: Hsteps. apply: bwp_progress => inv_G.
  iMod H as "(%zoo_G & %Φ & <- & Hinterp & H)".
  iExists zoo_G, [Φ]. iFrameSteps.
Qed.
Lemma bwp_adequacy `{zoo_Gpre : !ZooGpre Σ} {e σ} param :
  state_wf σ param →
  ( ∀ `{zoo_G : !ZooG Σ},
    ⊢ ∃ Φ,
      ([∗ map] l ↦ v ∈ state_heap_initial σ, l ↦ v) -∗
      0 ↦ₗ param.(zoo_parameter_local) -∗
      BWP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros Hwf Hwp.
  apply: bwp_adequacy' => // Hinv_G κs.
  iMod (zoo_init σ param κs) as "(%zoo_G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iDestruct (Hwp zoo_G) as "(%Φ & Hwp)".
  iExists zoo_G, Φ. iFrameSteps.
Qed.
