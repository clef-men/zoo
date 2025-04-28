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

Notation "'data'" := (
  in_type "zoo_std.queue_3.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_std.queue_3.t" 1
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_std.queue_3.t" 2
)(in custom zoo_field
).
