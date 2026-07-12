Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_bdeques_public.
Require Import zoo_parabs.waiters.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_std.optional.
Require Import zoo_std.int.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'deques'" := (
  in_type "zoo_parabs.ws_hub_hybrid.t" 0
)(in custom zoo_field
).
Notation "'rounds'" := (
  in_type "zoo_parabs.ws_hub_hybrid.t" 1
)(in custom zoo_field
).
Notation "'queue'" := (
  in_type "zoo_parabs.ws_hub_hybrid.t" 2
)(in custom zoo_field
).
Notation "'waiters'" := (
  in_type "zoo_parabs.ws_hub_hybrid.t" 3
)(in custom zoo_field
).
Notation "'num_active'" := (
  in_type "zoo_parabs.ws_hub_hybrid.t" 4
)(in custom zoo_field
).
