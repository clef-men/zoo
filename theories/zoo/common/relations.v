Require Export stdpp.relations.

Require Import zoo.prelude.
Require Import zoo.options.

Section relation.
  Context {A} (R : relation A).

  Lemma transitive𑁒tc `{!Transitive R} x1 x2 :
    tc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply tc_once.
  Qed.
  Lemma preorder𑁒rtc `{!Reflexive R} `{!Transitive R} x1 x2 :
    rtc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply rtc_once.
  Qed.

  #[global] Instance transitive𑁒tc𑁒antisymm `{!Transitive R} `{!AntiSymm R' R} :
    AntiSymm R' (tc R).
  Proof.
    intros x1 x2 H1%transitive𑁒tc H2%transitive𑁒tc. naive_solver.
  Qed.
  #[global] Instance preorder𑁒rtc𑁒antisymm `{!Reflexive R} `{!Transitive R} `{!AntiSymm R' R} :
    AntiSymm R' (rtc R).
  Proof.
    intros x1 x2 H1%preorder𑁒rtc H2%preorder𑁒rtc. naive_solver.
  Qed.

  Lemma rtc𑁒equivalence𑁒antisymm R' `{!Equivalence R'} `{!AntiSymm (=) (rtc R)} :
    AntiSymm R' (rtc R).
  Proof.
    intros a1 a2 ? ?. rewrite (anti_symm _ a1 a2) //.
  Qed.
End relation.

Class Initial {A} (R : relation A) :=
  { initial : A
  ; initial𑁒lb a :
      R initial a
  }.
#[global] Arguments Build_Initial {_ _} _ _ : assert.
#[global] Arguments initial {_ _ _} : assert.

#[global] Program Instance rtc𑁒initial `(R : relation A) `{!Initial R} : Initial (rtc R) :=
  {|initial := initial
  |}.
Next Obligation.
  intros A R ? a.
  apply rtc_once, initial𑁒lb.
Qed.
