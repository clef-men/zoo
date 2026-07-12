Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.waiters.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo.options.

Notation "'size'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 0
)(in custom zoo_field
).
Notation "'queue'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 1
)(in custom zoo_field
).
Notation "'waiters'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 2
)(in custom zoo_field
).
Notation "'num_active'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 3
)(in custom zoo_field
).
