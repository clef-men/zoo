From iris.algebra Require Export
  auth.

From zoo Require Import
  prelude.
From zoo.iris.algebra Require Export
  base.
From zoo.iris.algebra Require Import
  view.
From zoo Require Import
  options.

Section ucmra.
  Context {SI : sidx}.
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
