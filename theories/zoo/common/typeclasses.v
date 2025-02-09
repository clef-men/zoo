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
  @similar X
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≈)" :=
  similar
( only parsing
) : stdpp_scope.
Notation "(≈@{ A } )" := (
  @similar A
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

Class Nonsimilar X :=
  nonsimilar : X → X → Prop.
#[global] Arguments nonsimilar {_ _} !_ !_ / : simpl nomatch, assert.
Infix "≉" :=
  nonsimilar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "≉@{ X }" := (
  @nonsimilar X
)(at level 70,
  only parsing,
  no associativity
) : stdpp_scope.
Notation "(≉)" :=
  nonsimilar
( only parsing
) : stdpp_scope.
Notation "(≉@{ A } )" := (
  @nonsimilar A
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
