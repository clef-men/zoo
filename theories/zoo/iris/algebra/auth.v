Require Export iris.algebra.auth.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.iris.algebra.view.
Require Import zoo.options.

Section ucmra.
  Context {SI : sidx}.
  Context {A : ucmra}.

  Implicit Type a b : A.

  Lemma authｰauthｰfragｰdfracｰop dq1 a1 b1 dq2 a2 b2 :
    ●{dq1} a1 ⋅ ◯ b1 ≡ ●{dq2} a2 ⋅ ◯ b2 ↔
    dq1 = dq2 ∧ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    apply viewｰauthｰfragｰdfracｰop.
  Qed.
  Lemma authｰauthｰfragｰop a1 b1 a2 b2 :
    ● a1 ⋅ ◯ b1 ≡ ● a2 ⋅ ◯ b2 ↔
    a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    rewrite authｰauthｰfragｰdfracｰop. naive_solver.
  Qed.
End ucmra.
