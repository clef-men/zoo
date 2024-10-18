From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  int
  array.
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
