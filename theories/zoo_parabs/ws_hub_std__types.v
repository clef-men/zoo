From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  random_round
  optional
  int
  domain.
From zoo_parabs Require Import
  ws_deques_public
  waiters.
From zoo Require Import
  options.

Notation "'deques'" := (
  in_type "zoo_parabs.ws_hub_std.t" 0
)(in custom zoo_field
).
Notation "'rounds'" := (
  in_type "zoo_parabs.ws_hub_std.t" 1
)(in custom zoo_field
).
Notation "'waiters'" := (
  in_type "zoo_parabs.ws_hub_std.t" 2
)(in custom zoo_field
).
Notation "'killed'" := (
  in_type "zoo_parabs.ws_hub_std.t" 3
)(in custom zoo_field
).
