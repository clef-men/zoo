Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.diverge.
Require Import zoo_std.array.
Require Import zoo_std.assume.
Require Import zoo_std.int.
Require Import zoo.options.

Notation "'Empty'" := (
  in_type "zoo_std.dynarray_2.slot" 0
)(in custom zoo_tag
).
Notation "'Element'" := (
  in_type "zoo_std.dynarray_2.slot" 1
)(in custom zoo_tag
).

Notation "'value'" := (
  in_type "zoo_std.dynarray_2.slot.Element" 0
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
