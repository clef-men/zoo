From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst
  domain.
From zoo Require Import
  options.

Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).
