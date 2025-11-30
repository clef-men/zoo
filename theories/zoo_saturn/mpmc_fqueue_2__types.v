From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  atomic_array
  optional.
From zoo Require Import
  options.

Notation "'capacity'" := (
  in_type "zoo_saturn.mpmc_fqueue_2.t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.mpmc_fqueue_2.t" 1
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.mpmc_fqueue_2.t" 2
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.mpmc_fqueue_2.t" 3
)(in custom zoo_field
).
