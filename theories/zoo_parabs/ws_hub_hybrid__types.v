From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  ws_bdeques_public
  waiters.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_std Require Import
  array
  random_round
  optional
  int
  domain.
From zoo Require Import
  options.

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
