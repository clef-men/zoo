From stdpp Require Export
  relations.

From zebre Require Import
  prelude.
From zebre Require Import
  options.

#[global] Instance ge_partialorder :
  PartialOrder ge.
Proof.
  split; first split.
  - auto.
  - intros ?**. lia.
  - intros ?**. lia.
Qed.

Section relation.
  Context `(R : relation A).

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

  #[global] Instance transitive_tc_antisymm `{!Transitive R} `{!AntiSymm (=) R} :
    AntiSymm (=) (tc R).
  Proof.
    intros x1 x2 H1%transitive_tc H2%transitive_tc. naive_solver.
  Qed.
  #[global] Instance preorder_rtc_antisymm `{!PreOrder R} `{!AntiSymm (=) R} :
    AntiSymm (=) (rtc R).
  Proof.
    intros x1 x2 H1%preorder_rtc H2%preorder_rtc. naive_solver.
  Qed.
End relation.
