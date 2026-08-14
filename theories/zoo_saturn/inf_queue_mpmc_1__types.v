Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Export zoo_std.domain.
Require Export zoo_std.inf_array.
Require Export zoo_std.int.
Require Export zoo_std.optional.
Require Import zoo.options.

Notation "'data'" := (
  in_type "zoo_saturn.inf_queue_mpmc_1.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.inf_queue_mpmc_1.t" 1
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.inf_queue_mpmc_1.t" 2
)(in custom zoo_field
).
