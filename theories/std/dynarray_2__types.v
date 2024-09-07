From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  assume
  array
  math
  diverge.
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
