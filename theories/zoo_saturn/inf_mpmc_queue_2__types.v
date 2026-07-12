Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Import zoo_std.domain.
Require Import zoo.program_logic.identifier.
Require Import zoo.options.

Notation "'data'" := (
  in_type "zoo_saturn.inf_mpmc_queue_2.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.inf_mpmc_queue_2.t" 1
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.inf_mpmc_queue_2.t" 2
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_saturn.inf_mpmc_queue_2.t" 3
)(in custom zoo_field
).
