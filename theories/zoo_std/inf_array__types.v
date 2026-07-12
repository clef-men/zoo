Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex.
Require Import zoo_std.array.
Require Import zoo_std.int.
Require Import zoo.options.

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
