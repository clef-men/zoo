From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_parabs Require Export
  base
  ws_hub_fifo__code.
From zoo_parabs Require Import
  ws_hub_fifo__types.
From zoo Require Import
  options.

#[global] Opaque ws_hub_fifo_create.
#[global] Opaque ws_hub_fifo_killed.
#[global] Opaque ws_hub_fifo_push.
#[global] Opaque ws_hub_fifo_pop.
#[global] Opaque ws_hub_fifo_steal_until.
#[global] Opaque ws_hub_fifo_steal.
#[global] Opaque ws_hub_fifo_kill.
#[global] Opaque ws_hub_fifo_pop_steal_until.
#[global] Opaque ws_hub_fifo_pop_steal.
