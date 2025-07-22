From iris.algebra Require Export
  view.

From zoo Require Import
  prelude.
From zoo.iris.algebra Require Export
  base.
From zoo Require Import
  options.

Section cmra.
  Context {SI : sidx}.
  Context `(rel : view_rel A B).

  Implicit Types a : A.
  Implicit Types b : B.

  Lemma view_auth_frag_dfrac_op dq1 a1 b1 dq2 a2 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≡@{view rel} ●V{dq2} a2 ⋅ ◯V b2 ↔
    dq1 = dq2 ∧ a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    split.
    - intros (Hauth & Hfrag).
      rewrite /= !left_id in Hfrag. rewrite /= !right_id in Hauth.
      apply (inj Some) in Hauth as (-> & ->%(inj to_agree)). done.
    - intros (-> & -> & ->). done.
  Qed.
  Lemma view_auth_frag_op a1 b1 a2 b2 :
    ●V a1 ⋅ ◯V b1 ≡@{view rel} ●V a2 ⋅ ◯V b2 ↔
    a1 ≡ a2 ∧ b1 ≡ b2.
  Proof.
    rewrite view_auth_frag_dfrac_op. naive_solver.
  Qed.
End cmra.
