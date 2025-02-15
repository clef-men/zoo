From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex
  array
  int.
From zoo Require Import
  options.

Notation "'data'" := (
  in_type "zoo_std.inf_array.t" 0
)(in custom zoo_field
).
Notation "'default'" := (
  in_type "zoo_std.inf_array.t" 1
)(in custom zoo_field
).
Notation "'mutex'" := (
  in_type "zoo_std.inf_array.t" 2
)(in custom zoo_field
).
