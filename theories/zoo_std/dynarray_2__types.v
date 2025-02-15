From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  diverge
  array
  assume
  int.
From zoo Require Import
  options.

Notation "'Empty'" := (
  in_type "zoo_std.dynarray_2.slot" 0
)(in custom zoo_tag
).
Notation "'Element'" := (
  in_type "zoo_std.dynarray_2.slot" 1
)(in custom zoo_tag
).

Notation "'value'" := (
  in_type "zoo_std.dynarray_2.slot__Element" 0
)(in custom zoo_field
).

Notation "'size'" := (
  in_type "zoo_std.dynarray_2.t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_std.dynarray_2.t" 1
)(in custom zoo_field
).
