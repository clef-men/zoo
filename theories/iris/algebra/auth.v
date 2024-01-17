From iris.algebra Require Export
  auth.

From zebre Require Import
  prelude.
From zebre.iris.algebra Require Export
  base.
From zebre.iris.algebra Require Import
  view.
From zebre Require Import
  options.

Section ucmra.
  Context {A : ucmra}.

  Implicit Types a b : A.

  Lemma auth_auth_frag_dfrac_op dq1 a1 b1 dq2 a2 b2 :
    ●{dq1} a1 ⋅ ◯ b1 ≡ ●{dq2} a2 ⋅ ◯ b2 ↔
    dq1 = dq2 ∧ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    apply view_auth_frag_dfrac_op.
  Qed.
  Lemma auth_auth_frag_op a1 b1 a2 b2 :
    ● a1 ⋅ ◯ b1 ≡ ● a2 ⋅ ◯ b2 ↔
    a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    rewrite auth_auth_frag_dfrac_op. naive_solver.
  Qed.
End ucmra.
