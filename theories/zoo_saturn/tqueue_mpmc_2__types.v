Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Export zoo_std.atomic_array.
Require Export zoo_std.optional.
Require Import zoo.options.

Notation "'capacity'" := (
  in_type "zoo_saturn.tqueue_mpmc_2.t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.tqueue_mpmc_2.t" 1
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.tqueue_mpmc_2.t" 2
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.tqueue_mpmc_2.t" 3
)(in custom zoo_field
).
