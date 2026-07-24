Require Export iris.algebra.view.

Require Import zoo.prelude.
Require Export zoo.iris.algebra.base.
Require Import zoo.options.

Section cmra.
  Context {SI : sidx}.
  Context `(rel : view_rel A B).

  Implicit Type a : A.
  Implicit Type b : B.

  Lemma view𑁒auth𑁒frag𑁒dfrac𑁒op dq1 a1 b1 dq2 a2 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≡@{view rel} ●V{dq2} a2 ⋅ ◯V b2 ↔
    dq1 = dq2 ∧ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    split.
    - intros (Hauth & Hfrag).
      rewrite /= !left_id in Hfrag. rewrite /= !right_id in Hauth.
      apply (inj Some) in Hauth as (-> & ->%(inj to_agree)). done.
    - intros (-> & -> & ->). done.
  Qed.
  Lemma view𑁒auth𑁒frag𑁒op a1 b1 a2 b2 :
    ●V a1 ⋅ ◯V b1 ≡@{view rel} ●V a2 ⋅ ◯V b2 ↔
    a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    rewrite view𑁒auth𑁒frag𑁒dfrac𑁒op. naive_solver.
  Qed.
End cmra.
