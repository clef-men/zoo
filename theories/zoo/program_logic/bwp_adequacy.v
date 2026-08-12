Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.diaframe.
Require Export zoo.program_logic.bwp.
Require Import zoo.options.

Implicit Type e : expr.
Implicit Type es : list expr.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.
  Implicit Type Φs : list (val → iProp Σ).

  Definition bwps nt es Φs : iProp Σ :=
    [∗ list] i ↦ e; Φ ∈ es; Φs,
      BWP e ∶ nt + i {{ Φ }}.

  #[local] Lemma bwpｰstep tid e1 σ1 e2 σ2 κ κs es ns nt Φ :
    prim_step tid e1 σ1 κ e2 σ2 es →
    state_interp ns nt σ1 (κ ++ κs) -∗
    £ (later۰function ns) -∗
    BWP e1 ∶ tid {{ Φ }} -∗
      |={⊤}[∅]▷=>
      state_interp ˖ns (nt + length es) σ2 κs ∗
      BWP e2 ∶ tid {{ Φ }} ∗
      bwps nt es (replicate (length es) fork_post).
  Proof.
    iIntros "%Hstep Hinterp H£ H".
    rewrite {1}bwpｰunfold /bwp۰pre (prim_stepｰnot_val tid e1 σ1 κ e2 σ2 es) //.
    iMod ("H" with "Hinterp") as "(_ & >H)".
    iMod ("H" with "[//] [//] H£") as "H".
    iModIntro.
    iSteps. rewrite /bwps big_sepL2_replicate_r //.
  Qed.
  #[local] Lemma bwpsｰstep es1 σ1 es2 σ2 κ κs ns Φs :
    step (es1, σ1) κ (es2, σ2) →
    state_interp ns (length es1) σ1 (κ ++ κs) -∗
    £ (later۰function ns) -∗
    bwps 0 es1 Φs -∗
      |={⊤}[∅]▷=>
      state_interp ˖ns (length es2) σ2 κs ∗
      bwps 0 es2 (Φs ++ replicate (length es2 - length es1) fork_post).
  Proof.
    iIntros ((i & e1 & e2 & σ2' & es & Hstep & Hes1_lookup & [= -> <-])) "Hinterp H£ H".
    iDestruct (big_sepL2ｰinsertｰaccｰl with "H") as "(%Φ & %HΦs_lookup & He1 & H)"; first done.
    iMod (bwpｰstep with "Hinterp H£ He1") as "He1"; first done.
    do 2 iModIntro.
    iMod "He1" as "(Hinterp & He2 & Hes)".
    iDestruct ("H" with "He2") as "H".
    simp_length. rewrite Nat.add_sub' (list_insert_id Φs) // big_sepL2_app. simp_length.
    iSteps.
  Qed.
  #[local] Lemma bwpsｰsteps n es1 σ1 es2 σ2 κs1 κs2 ns Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    state_interp ns (length es1) σ1 (κs1 ++ κs2) -∗
    £ (later۰sum ns n) -∗
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
      iMod (bwpsｰstep with "Hinterp H£ H") as "H"; [done.. |].
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
      { apply stepｰlength in Hstep.
        apply nstepsｰlength in Hsteps'.
        naive_solver lia.
      }
      iFrameSteps.
  Qed.

  #[local] Lemma bwpｰnotｰstuck e tid ns nt σ κs Φ :
    state_interp ns nt σ κs -∗
    BWP e ∶ tid {{ Φ }} -∗
      |={⊤, ∅}=>
      ⌜not_stuck tid e σ⌝.
  Proof.
    iIntros "Hinterp H".
    rewrite bwpｰunfold /bwp۰pre /not_stuck.
    destruct (to_val e) as [v |] eqn:He.
    - iMod (fupd_mask_subseteq ∅); first done.
      iSteps.
    - iMod ("H" with "Hinterp") as ">(%Hreducible & _)".
      iSteps.
  Qed.

  #[local] Lemma bwpsｰprogress n es1 σ1 tid e2 es2 σ2 κs1 κs2 ns Φs :
    nsteps n (es1, σ1) κs1 (es2, σ2) →
    es2 !! tid = Some e2 →
    state_interp ns (length es1) σ1 (κs1 ++ κs2) -∗
    £ (later۰sum ns n) -∗
    bwps 0 es1 Φs -∗
      |={⊤, ∅}=> |={∅}▷=>^n |={∅}=>
      ⌜not_stuck tid e2 σ2⌝.
  Proof.
    iIntros (Hsteps Hes2_lookup) "Hinterp H£s He".
    iMod (bwpsｰsteps with "Hinterp H£s He") as "H"; [done.. |].
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "(Hinterp & H)".
    iDestruct (big_sepL2ｰlookupｰSomeｰl with "H") as %(Φ & Hposts_lookup); first done.
    iDestruct (big_sepL2_lookup with "H") as "H"; [done.. |].
    iApply (bwpｰnotｰstuck with "Hinterp H").
  Qed.
End zoo۰G.

Lemma bwpｰprogress `{inv_Gpre : !invGpreS Σ} n es1 σ1 es2 σ2 κs :
  ( ∀ `{inv۰G : !invGS Σ},
    ⊢ |={⊤}=>
      ∃ (zoo۰G : ZooG Σ) Φs,
      ⌜zoo۰G.(zoo۰G۰inv۰G) = inv۰G⌝ ∗
      state_interp 0 (length es1) σ1 κs ∗
      bwps 0 es1 Φs
  ) →
  nsteps n (es1, σ1) κs (es2, σ2) →
  Foralli (λ tid e2, not_stuck tid e2 σ2) es2.
Proof.
  intros H Hsteps.
  apply Foralliｰlookup => tid e2 Hlookup.
  apply (pure_soundness (PROP := iPropI Σ)), (step_fupdN_soundness_lc _ n (later۰sum 0 n)).
  iIntros "%Hinv_G H£s".
  iMod H as "(%zoo۰G & %Φs & <- & Hinterp & H)".
  iMod (bwpsｰprogress with "[Hinterp] H£s H") as "H". 1,2: done.
  { erewrite app_nil_r => //. }
  destruct n.
  - iMod "H". iSteps.
  - iApply step_fupdN_S_fupd. iSteps.
Qed.

Lemma bwpｰadequacy' `{inv_Gpre : !invGpreS Σ} e σ :
  ( ∀ `{inv۰G : !invGS Σ} κs,
    ⊢ |={⊤}=>
      ∃ (zoo۰G : ZooG Σ) Φ,
      ⌜zoo۰G.(zoo۰G۰inv۰G) = inv۰G⌝ ∗
      state_interp 0 1 σ κs ∗
      BWP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros H (es, σ') (n & κs & Hsteps)%silent_stepsｰnsteps.
  move: Hsteps. apply: bwpｰprogress => inv۰G.
  iMod H as "(%zoo۰G & %Φ & <- & Hinterp & H)".
  iExists zoo۰G, [Φ]. iFrameSteps.
Qed.
Lemma bwpｰadequacy `{zoo۰Gpre : !ZooGpre Σ} {e σ} v :
  state۰wf σ v →
  ( ∀ `{zoo۰G : !ZooG Σ},
    ⊢ ∃ Φ,
      ([∗ map] l ↦ v ∈ state۰heap۰initial σ, l ↦ v) -∗
      0 ↦ₗ v -∗
      BWP e ∶ 0 {{ Φ }}
  ) →
  safe ([e], σ).
Proof.
  intros Hwf Hwp.
  apply: bwpｰadequacy' => // Hinv_G κs.
  iMod (state_interpｰinit σ v κs) as "(%zoo۰G & <- & Hinterp & Hheap & Hlocals)"; first done.
  iDestruct (Hwp zoo۰G) as "(%Φ & Hwp)".
  iExists zoo۰G, Φ. iFrameSteps.
Qed.
