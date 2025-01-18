From zoo Require Import
  prelude.
From zoo_saturn Require Export
  base
  inf_mpmc_queue_2__code.
From zoo_saturn Require Import
  inf_mpmc_queue_2__types.
From zoo Require Import
  options.

#[global] Opaque inf_mpmc_queue_2_create.
#[global] Opaque inf_mpmc_queue_2_size.
#[global] Opaque inf_mpmc_queue_2_is_empty.
#[global] Opaque inf_mpmc_queue_2_push.
#[global] Opaque inf_mpmc_queue_2_pop.
