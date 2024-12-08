From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Nil'" := (
  in_type "lst" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "lst" 1
)(in custom zoo_tag
).

Notation "'capacity'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "t" 1
)(in custom zoo_field
).
