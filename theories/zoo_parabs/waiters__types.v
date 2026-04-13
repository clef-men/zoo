From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  waiter.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_std Require Import
  array.
From zoo Require Import
  options.

Notation "'waiters'" := (
  in_type "zoo_parabs.waiters.t" 0
)(in custom zoo_proj
).
Notation "'queue'" := (
  in_type "zoo_parabs.waiters.t" 1
)(in custom zoo_proj
).
