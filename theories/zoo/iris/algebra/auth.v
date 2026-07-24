Require Export iris.algebra.auth.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.view.
Require Import zoo.options.

Section ucmra.
  Context {SI : sidx}.
  Context {A : ucmra}.

  Implicit Type a b : A.

  Lemma auth𑁒auth𑁒frag𑁒dfrac𑁒op dq1 a1 b1 dq2 a2 b2 :
    ●{dq1} a1 ⋅ ◯ b1 ≡ ●{dq2} a2 ⋅ ◯ b2 ↔
    dq1 = dq2 ∧ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    apply view𑁒auth𑁒frag𑁒dfrac𑁒op.
  Qed.
  Lemma auth𑁒auth𑁒frag𑁒op a1 b1 a2 b2 :
    ● a1 ⋅ ◯ b1 ≡ ● a2 ⋅ ◯ b2 ↔
    a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    rewrite auth𑁒auth𑁒frag𑁒dfrac𑁒op. naive_solver.
  Qed.
End ucmra.
