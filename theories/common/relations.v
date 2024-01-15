From stdpp Require Export
  relations.

From zebra Require Import
  prelude.
From zebra Require Import
  options.

#[global] Instance ge_reflexive :
  Reflexive ge.
Proof.
  auto.
Qed.
#[global] Instance ge_transitive :
  Transitive ge.
Proof.
  intros ?**. lia.
Qed.
#[global] Instance ge_antisymm :
  AntiSymm (=) ge.
Proof.
  intros ?**. lia.
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
  Lemma reflexive_transitive_rtc `{!Reflexive R} `{!Transitive R} x1 x2 :
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
  #[global] Instance reflexive_transitive_rtc_antisymm `{!Reflexive R} `{!Transitive R} `{!AntiSymm (=) R} :
    AntiSymm (=) (rtc R).
  Proof.
    intros x1 x2 H1%reflexive_transitive_rtc H2%reflexive_transitive_rtc. naive_solver.
  Qed.
End relation.
