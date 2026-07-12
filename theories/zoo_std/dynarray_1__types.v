Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo.options.

Notation "'size'" := (
  in_type "zoo_std.dynarray_1.t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_std.dynarray_1.t" 1
)(in custom zoo_field
).
