Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_deques_public.
Require Import zoo_parabs.waiters.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_std.optional.
Require Import zoo_std.int.
Require Import zoo_std.domain.
Require Import zoo.options.

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
Notation "'num_active'" := (
  in_type "zoo_parabs.ws_hub_std.t" 3
)(in custom zoo_field
).
