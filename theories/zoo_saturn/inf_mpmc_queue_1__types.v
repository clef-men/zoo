From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  inf_array
  int
  optional
  domain.
From zoo Require Import
  options.

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
