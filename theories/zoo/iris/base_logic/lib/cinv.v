Require Export iris.base_logic.lib.cancelable_invariants.

Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.iris.bi.big_op.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Section cinv۰G.
  Context `{inv۰G : !invGS Σ}.
  Context `{cinv۰G : !cinvG Σ}.

  Lemma cinv_ownｰdivide {γ q} n :
    n ≠ 0 →
    cinv_own γ q ⊢
    [∗ list] _ ∈ seq 0 n, cinv_own γ (q / Qp۰of_nat n).
  Proof.
    iIntros "%Hn Hown".
    iInduction n as [| n IH] forall (q).
    - lia.
    - clear Hn. destruct_decide (n = 0) as -> | Hn.
      + iEval (rewrite Qp۰of_natｰ1 Qp.div_1).
        iSteps.
      + assert (q = q / (1 + Qp۰of_nat n) + (q * Qp۰of_nat n / (1 + Qp۰of_nat n)))%Qp as Heq.
        { rewrite -Qp.div_add_distr -{2}(Qp.mul_1_r q) -Qp.mul_add_distr_l.
          rewrite -{2}(Qp.mul_1_l (1 + _)).
          rewrite Qp.div_mul_cancel_r Qp.div_1 //.
        }
        iEval (setoid_rewrite Heq) in "Hown". clear Heq.
        iEval (rewrite Qp۰of_natｰS //).
        iDestruct (fractional with "Hown") as "($ & Hown)".
        iEval (rewrite -/seq).
        iDestruct ("IH" with "[//] Hown") as "Howns".
        iEval (rewrite Qp.div_div Qp.div_mul_cancel_r) in "Howns".
        iApply big_sepLｰseqｰshiftｰ1.
        iFrame.
  Qed.
  Lemma cinv_ownｰgather γ q n :
    n ≠ 0 →
    ([∗ list] _ ∈ seq 0 n, cinv_own γ (q / Qp۰of_nat n)) ⊢
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
      + assert (q = q / (1 + Qp۰of_nat n) + (q * Qp۰of_nat n / (1 + Qp۰of_nat n)))%Qp as Heq.
        { rewrite -Qp.div_add_distr -{2}(Qp.mul_1_r q) -Qp.mul_add_distr_l.
          rewrite -{2}(Qp.mul_1_l (1 + _)).
          rewrite Qp.div_mul_cancel_r Qp.div_1 //.
        }
        iEval (setoid_rewrite Heq). clear Heq.
        iEval (rewrite Qp۰of_natｰS //) in "Hown Howns".
        iSplitL "Hown". 1: iFrame.
        iDestruct (big_sepLｰseqｰshiftｰ1₁ with "Howns") as "Howns".
        iEval (rewrite -(Qp.div_mul_cancel_r _ _ (Qp۰of_nat n)) -Qp.div_div) in "Howns".
        iApply ("IH" with "[//] Howns").
  Qed.
End cinv۰G.
