From zoo Require Import
  prelude.
From zoo Require Import
  options.

Class Similar X :=
  similar : X → X → Prop.
#[global] Arguments similar {_ _} !_ !_ / : simpl nomatch, assert.
Infix "≈" :=
  similar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "≈@{ X }" := (
  @similar X _
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≈)" :=
  similar
( only parsing
) : stdpp_scope.
Notation "(≈@{ X } )" := (
  @similar X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≈.)" := (
  similar x1
)(only parsing
) : stdpp_scope.
Notation "(.≈ x2 )" := (
  λ x1, similar x1 x2
)(only parsing
) : stdpp_scope.

#[global] Instance list_similar X `{!Similar X} : Similar (list X) :=
  Forall2 similar.

Class Nonsimilar X :=
  nonsimilar : X → X → Prop.
#[global] Arguments nonsimilar {_ _} !_ !_ / : simpl nomatch, assert.
Infix "≉" :=
  nonsimilar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "≉@{ X }" := (
  @nonsimilar X _
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≉)" :=
  nonsimilar
( only parsing
) : stdpp_scope.
Notation "(≉@{ X } )" := (
  @nonsimilar X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≉.)" := (
  nonsimilar x1
)(only parsing
) : stdpp_scope.
Notation "(.≉ x2 )" := (
  λ x1, nonsimilar x1 x2
)(only parsing
) : stdpp_scope.

Class Beq {X} := {
  beq : X → X → bool ;
  beq_spec x1 x2 :
    beq x1 x2 = true ↔
    x1 = x2 ;
}.
#[global] Arguments Beq : clear implicits.
#[global] Arguments beq {_ _} !_ !_ / : simpl nomatch, assert.

Infix "≟" :=
  beq
( at level 30,
  no associativity
) : stdpp_scope.
Infix "≟@{ X }" := (
  @beq X _
)(at level 30,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≟)" :=
  beq
( only parsing
) : stdpp_scope.
Notation "(≟@{ X } )" := (
  @beq X _
)( only parsing
) : stdpp_scope.
Notation "( x1 ≟.)" := (
  beq x1
)(only parsing
) : stdpp_scope.
Notation "(.≟ x2 )" := (
  λ x1, beq x1 x2
)(only parsing
) : stdpp_scope.

Section beq.
  Context `{!Beq X}.

  Lemma beq_spec' x1 x2 :
    x1 ≟ x2 = false ↔
    x1 ≠ x2.
  Proof.
    rewrite -beq_spec not_true_iff_false //.
  Qed.

  Lemma beq_eq x1 x2 :
    x1 ≟ x2 = true →
    x1 = x2.
  Proof.
    apply beq_spec.
  Qed.
  Lemma beq_ne x1 x2 :
    x1 ≟ x2 = false →
    x1 ≠ x2.
  Proof.
    apply beq_spec'.
  Qed.

  Lemma beq_true x1 x2 :
    x1 = x2 →
    x1 ≟ x2 = true.
  Proof.
    apply beq_spec.
  Qed.
  Lemma beq_true' x :
    x ≟ x = true.
  Proof.
    apply beq_true. done.
  Qed.
  Lemma beq_false x1 x2 :
    x1 ≠ x2 →
    x1 ≟ x2 = false.
  Proof.
    apply beq_spec'.
  Qed.
End beq.

#[global] Program Instance bool_beq : Beq bool := {|
  beq := Bool.eqb ;
|}.
Next Obligation.
  apply Bool.eqb_true_iff.
Qed.

#[global] Program Instance nat_beq : Beq nat := {|
  beq := Nat.eqb ;
|}.
Next Obligation.
  apply Nat.eqb_eq.
Qed.

#[global] Program Instance Z_beq : Beq Z := {|
  beq := Z.eqb ;
|}.
Next Obligation.
  apply Z.eqb_eq.
Qed.
