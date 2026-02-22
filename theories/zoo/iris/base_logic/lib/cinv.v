From iris.base_logic Require Export
  lib.cancelable_invariants.

From zoo Require Import
  prelude.
From zoo.common Require Import
  math.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Section cinv_G.
  Context `{inv_G : !invGS Σ}.
  Context `{cinv_G : !cinvG Σ}.

  Lemma cinv_own_divide {γ q} n :
    n ≠ 0 →
    cinv_own γ q ⊢
    [∗ list] _ ∈ seq 0 n, cinv_own γ (q / Qp_of_nat n).
  Proof.
    iIntros "%Hn Hown".
    iInduction n as [| n IH] forall (q).
    - lia.
    - clear Hn. destruct_decide (n = 0) as -> | Hn.
      + iEval (rewrite Qp_of_nat_1 Qp.div_1).
        iSteps.
      + assert (q = q / (1 + Qp_of_nat n) + (q * Qp_of_nat n / (1 + Qp_of_nat n)))%Qp as Heq.
        { rewrite -Qp.div_add_distr -{2}(Qp.mul_1_r q) -Qp.mul_add_distr_l.
          rewrite -{2}(Qp.mul_1_l (1 + _)).
          rewrite Qp.div_mul_cancel_r Qp.div_1 //.
        }
        iEval (setoid_rewrite Heq) in "Hown". clear Heq.
        iEval (rewrite Qp_of_nat_S //).
        iDestruct (fractional with "Hown") as "($ & Hown)".
        iEval (rewrite -/seq).
        iDestruct ("IH" with "[//] Hown") as "Howns".
        iEval (rewrite Qp.div_div Qp.div_mul_cancel_r) in "Howns".
        iApply big_sepL_seq_shift1.
        iFrame.
  Qed.
  Lemma cinv_own_gather γ q n :
    n ≠ 0 →
    ([∗ list] _ ∈ seq 0 n, cinv_own γ (q / Qp_of_nat n)) ⊢
    cinv_own γ q.
  Proof.
    iIntros "%Hn Howns".
    iInduction n as [| n IH] forall (q Hn).
    - lia.
    - iDestruct "Howns" as "(Hown & Howns)".
      iEval (rewrite -/seq) in "Howns".
      clear Hn. destruct_decide (n = 0) as -> | Hn.
      + iEval (rewrite Qp.div_1) in "Hown".
        iFrame.
      + assert (q = q / (1 + Qp_of_nat n) + (q * Qp_of_nat n / (1 + Qp_of_nat n)))%Qp as Heq.
        { rewrite -Qp.div_add_distr -{2}(Qp.mul_1_r q) -Qp.mul_add_distr_l.
          rewrite -{2}(Qp.mul_1_l (1 + _)).
          rewrite Qp.div_mul_cancel_r Qp.div_1 //.
        }
        iEval (setoid_rewrite Heq). clear Heq.
        iEval (rewrite Qp_of_nat_S //) in "Hown Howns".
        iSplitL "Hown". 1: iFrame.
        iDestruct (big_sepL_seq_shift1_1 with "Howns") as "Howns".
        iEval (rewrite -(Qp.div_mul_cancel_r _ _ (Qp_of_nat n)) -Qp.div_div) in "Howns".
        iApply ("IH" with "[//] Howns").
  Qed.
End cinv_G.
