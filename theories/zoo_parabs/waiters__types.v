Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.waiter.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'waiters'" := (
  in_type "zoo_parabs.waiters.t" 0
)(in custom zoo_proj
).
Notation "'queue'" := (
  in_type "zoo_parabs.waiters.t" 1
)(in custom zoo_proj
).
