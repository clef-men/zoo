From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Import
  waiters.
From zoo Require Import
  options.

Notation "'queue'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 0
)(in custom zoo_field
).
Notation "'size'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 1
)(in custom zoo_field
).
Notation "'waiters'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 2
)(in custom zoo_field
).
Notation "'killed'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 3
)(in custom zoo_field
).
