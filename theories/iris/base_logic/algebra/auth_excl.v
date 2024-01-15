From iris.bi Require Import
  bi.
From iris.base_logic Require Import
  bi.

From zebra Require Import
  prelude.
From zebra.iris.algebra Require Import
  lib.auth_excl.
From zebra Require Import
  options.

Section upred.
  Context {M : ucmra}.

  Notation "P ⊢ Q" := (bi_entails (PROP := uPredI M) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A := uPredI M) P%I Q%I).
  Notation "⊢ Q" := (bi_entails (PROP := uPredI M) True Q).

  Section ofe.
    Context {A : ofe}.

    Implicit Types a b : A.

    Lemma auth_excl_auth_dfrac_validI dq a :
      ✓ (●E{dq} a) ⊣⊢
      ⌜✓ dq⌝.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= auth_excl_auth_dfrac_validN //.
    Qed.
    Lemma auth_excl_auth_validI a :
      ⊢ ✓ (●E a).
    Proof.
      rewrite auth_excl_auth_dfrac_validI bi.pure_True //.
    Qed.

    Lemma auth_excl_auth_dfrac_op_validI dq1 a1 dq2 a2 :
      ✓ (●E{dq1} a1 ⋅ ●E{dq2} a2) ⊣⊢
      ⌜✓ (dq1 ⋅ dq2)⌝ ∧ a1 ≡ a2.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= auth_excl_auth_dfrac_op_validN //.
    Qed.
    Lemma auth_excl_auth_op_validI a b :
      ✓ (●E a ⋅ ●E b) ⊣⊢
      False.
    Proof.
      rewrite auth_excl_auth_dfrac_op_validI bi.pure_False; first naive_solver.
      rewrite left_absorb //.
    Qed.

    Lemma auth_excl_frag_validI a :
      ⊢ ✓ (◯E a).
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= => _. apply auth_excl_frag_validN.
    Qed.

    Lemma auth_excl_frag_op_validI a b :
      ✓ (◯E a ⋅ ◯E b) ⊣⊢
      False.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= auth_excl_frag_op_validN //.
    Qed.

    Lemma auth_excl_both_dfrac_validI dq a b :
      ✓ (●E{dq} a ⋅ ◯E b) ⊣⊢
      ⌜✓ dq⌝ ∧ a ≡ b.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= auth_excl_both_dfrac_validN //.
    Qed.
    Lemma auth_excl_both_validI a b :
      ✓ (●E a ⋅ ◯E b) ⊣⊢
      a ≡ b.
    Proof.
      uPred.unseal. split=> n x Hx.
      rewrite /uPred_holds /= auth_excl_both_validN //.
    Qed.
  End ofe.
End upred.
