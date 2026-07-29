Require Import iris.bi.bi.
Require Import iris.base_logic.bi.

Require Import zoo.prelude.
Require Import zoo.iris.algebra.lib.twins.
Require Import zoo.options.

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

    Implicit Type a b : A.

    Lemma twins۰twin₁ｰdfracｰvalidI dq a :
      ✓ (twins۰twin₁ dq a) ⊣⊢
      ⌜✓ dq⌝.
    Proof.
      sbi_unfold => n.
      apply twins۰twin₁ｰdfracｰvalidN.
    Qed.
    Lemma twins۰twin₁ｰvalidI a :
      ⊢ ✓ (twins۰twin₁ (DfracOwn 1) a).
    Proof.
      rewrite twins۰twin₁ｰdfracｰvalidI bi.pure_True //.
    Qed.

    Lemma twins۰twin₁ｰdfracｰopｰvalidI dq1 a1 dq2 a2 :
      ✓ (twins۰twin₁ dq1 a1 ⋅ twins۰twin₁ dq2 a2) ⊣⊢
        ⌜✓ (dq1 ⋅ dq2)⌝ ∧
        a1 ≡ a2.
    Proof.
      sbi_unfold => n.
      apply twins۰twin₁ｰdfracｰopｰvalidN.
    Qed.
    Lemma twins۰twin₁ｰopｰvalidI a b :
      ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₁ (DfracOwn 1) b) ⊣⊢
      False.
    Proof.
      rewrite twins۰twin₁ｰdfracｰopｰvalidI bi.pure_False. 1: auto.
      rewrite left_absorb //.
    Qed.

    Lemma twins۰twin₂ｰvalidI a :
      ⊢ ✓ (twins۰twin₂ a).
    Proof.
      sbi_unfold => n _.
      apply twins۰twin₂ｰvalidN.
    Qed.

    Lemma twins۰twin₂ｰopｰvalidI a b :
      ✓ (twins۰twin₂ a ⋅ twins۰twin₂ b) ⊣⊢
      False.
    Proof.
      sbi_unfold => n.
      apply twins۰twin₂ｰopｰvalidN.
    Qed.

    Lemma twinsｰbothｰdfracｰvalidI dq a b :
      ✓ (twins۰twin₁ dq a ⋅ twins۰twin₂ b) ⊣⊢
        ⌜✓ dq⌝ ∧
        a ≡ b.
    Proof.
      sbi_unfold => n.
      apply twinsｰbothｰdfracｰvalidN.
    Qed.
    Lemma twinsｰbothｰvalidI a b :
      ✓ (twins۰twin₁ (DfracOwn 1) a ⋅ twins۰twin₂ b) ⊣⊢
      a ≡ b.
    Proof.
      sbi_unfold => n.
      apply twinsｰbothｰvalidN.
    Qed.
  End ofe.
End upred.
