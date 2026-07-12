Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'data'" := (
  in_type "zoo_saturn.inf_mpmc_queue_1.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.inf_mpmc_queue_1.t" 1
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.inf_mpmc_queue_1.t" 2
)(in custom zoo_field
).
