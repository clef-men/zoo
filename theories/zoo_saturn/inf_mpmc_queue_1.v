From zoo Require Import
  prelude.
From zoo_saturn Require Export
  base
  inf_mpmc_queue_1__code.
From zoo_saturn Require Import
  inf_mpmc_queue_1__types.
From zoo Require Import
  options.

#[global] Opaque inf_mpmc_queue_1_create.
#[global] Opaque inf_mpmc_queue_1_push.
#[global] Opaque inf_mpmc_queue_1_pop.
