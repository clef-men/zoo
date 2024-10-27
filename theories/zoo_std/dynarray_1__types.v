From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  int.
From zoo Require Import
  options.

Notation "'size'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "t" 1
)(in custom zoo_field
).
