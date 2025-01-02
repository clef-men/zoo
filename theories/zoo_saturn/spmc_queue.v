From zoo Require Import
  prelude.
From zoo_saturn Require Export
  base
  spmc_queue__code.
From zoo_saturn Require Import
  spmc_queue__types.
From zoo Require Import
  options.

#[global] Opaque spmc_queue_create.
#[global] Opaque spmc_queue_is_empty.
#[global] Opaque spmc_queue_push.
#[global] Opaque spmc_queue_pop.
