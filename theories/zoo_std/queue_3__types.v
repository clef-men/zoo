Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo.options.

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
