From stdpp Require Export
  relations.

From zebre Require Import
  prelude.
From zebre Require Import
  options.

Section relation.
  Context {A} (R : relation A).

  Lemma transitive_tc `{!Transitive R} x1 x2 :
    tc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply tc_once.
  Qed.
  Lemma preorder_rtc `{!PreOrder R} x1 x2 :
    rtc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply rtc_once.
  Qed.

  #[global] Instance transitive_tc_antisymm `{!Transitive R} `{!AntiSymm R' R} :
    AntiSymm R' (tc R).
  Proof.
    intros x1 x2 H1%transitive_tc H2%transitive_tc. naive_solver.
  Qed.
  #[global] Instance preorder_rtc_antisymm `{!PreOrder R} `{!AntiSymm R' R} :
    AntiSymm R' (rtc R).
  Proof.
    intros x1 x2 H1%preorder_rtc H2%preorder_rtc. naive_solver.
  Qed.

  Lemma rtc_equivalence_antisymm R' `{!Equivalence R'} `{!AntiSymm (=) (rtc R)} :
    AntiSymm R' (rtc R).
  Proof.
    intros a1 a2 ? ?. rewrite (anti_symm _ a1 a2) //.
  Qed.
End relation.
