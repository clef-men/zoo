From iris.bi Require Import
  bi.
From iris.base_logic Require Import
  bi.

From zoo Require Import
  prelude.
From zoo.iris.algebra Require Import
  lib.twins.
From zoo Require Import
  options.

Section upred.
  Context {M : ucmra}.

  Notation "P ⊢ Q" := (
    bi_entails (PROP := uPredI M) P Q
  ).
  Notation "P ⊣⊢ Q" := (
    equiv (A := uPredI M) P%I Q%I
  ).
  Notation "⊢ Q" := (
    bi_entails (PROP := uPredI M) True Q
  ).

  Section ofe.
    Context {A : ofe}.

    Implicit Types a b : A.

    Lemma twins_twin1_dfrac_validI dq a :
      ✓ (twins_twin1 dq a) ⊣⊢
      ⌜✓ dq⌝.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= twins_twin1_dfrac_validN //.
    Qed.
    Lemma twins_twin1_validI a :
      ⊢ ✓ (twins_twin1 (DfracOwn 1) a).
    Proof.
      rewrite twins_twin1_dfrac_validI bi.pure_True //.
    Qed.

    Lemma twins_twin1_dfrac_op_validI dq1 a1 dq2 a2 :
      ✓ (twins_twin1 dq1 a1 ⋅ twins_twin1 dq2 a2) ⊣⊢
      ⌜✓ (dq1 ⋅ dq2)⌝ ∧ a1 ≡ a2.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= twins_twin1_dfrac_op_validN //.
    Qed.
    Lemma twins_twin1_op_validI a b :
      ✓ (twins_twin1 (DfracOwn 1) a ⋅ twins_twin1 (DfracOwn 1) b) ⊣⊢
      False.
    Proof.
      rewrite twins_twin1_dfrac_op_validI bi.pure_False; first naive_solver.
      rewrite left_absorb //.
    Qed.

    Lemma twins_twin2_validI a :
      ⊢ ✓ (twins_twin2 a).
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= => _. apply twins_twin2_validN.
    Qed.

    Lemma twins_twin2_op_validI a b :
      ✓ (twins_twin2 a ⋅ twins_twin2 b) ⊣⊢
      False.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= twins_twin2_op_validN //.
    Qed.

    Lemma twins_both_dfrac_validI dq a b :
      ✓ (twins_twin1 dq a ⋅ twins_twin2 b) ⊣⊢
      ⌜✓ dq⌝ ∧ a ≡ b.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= twins_both_dfrac_validN //.
    Qed.
    Lemma twins_both_validI a b :
      ✓ (twins_twin1 (DfracOwn 1) a ⋅ twins_twin2 b) ⊣⊢
      a ≡ b.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= twins_both_validN //.
    Qed.
  End ofe.
End upred.
