Require Export stdpp.relations.

Require Import zoo.prelude.
Require Import zoo.options.

Section relation.
  Context {A} (R : relation A).

  Lemma transitiveｰtc `{!Transitive R} x1 x2 :
    tc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply tc_once.
  Qed.
  Lemma preorderｰrtc `{!Reflexive R} `{!Transitive R} x1 x2 :
    rtc R x1 x2 ↔
    R x1 x2.
  Proof.
    split.
    - induction 1; last etrans; done.
    - apply rtc_once.
  Qed.

  #[global] Instance transitiveｰtcｰantisymm `{!Transitive R} `{!AntiSymm R' R} :
    AntiSymm R' (tc R).
  Proof.
    intros x1 x2 H1%transitiveｰtc H2%transitiveｰtc. naive_solver.
  Qed.
  #[global] Instance preorderｰrtcｰantisymm `{!Reflexive R} `{!Transitive R} `{!AntiSymm R' R} :
    AntiSymm R' (rtc R).
  Proof.
    intros x1 x2 H1%preorderｰrtc H2%preorderｰrtc. naive_solver.
  Qed.

  Lemma rtcｰequivalenceｰantisymm R' `{!Equivalence R'} `{!AntiSymm (=) (rtc R)} :
    AntiSymm R' (rtc R).
  Proof.
    intros a1 a2 ? ?. rewrite (anti_symm _ a1 a2) //.
  Qed.
End relation.

Class Initial {A} (R : relation A) :=
  { initial : A
  ; initialｰlb a :
      R initial a
  }.
#[global] Arguments Build_Initial {_ _} _ _ : assert.
#[global] Arguments initial {_ _ _} : assert.

#[global] Program Instance rtcｰinitial `(R : relation A) `{!Initial R} : Initial (rtc R) :=
  {|initial := initial
  |}.
Next Obligation.
  intros A R ? a.
  apply rtc_once, initialｰlb.
Qed.
