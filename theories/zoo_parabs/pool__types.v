Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_hub_std.
Require Import zoo_std.ivar_4.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'context_size'" := (
  in_type "zoo_parabs.pool.context" 0
)(in custom zoo_proj
).
Notation "'context_hub'" := (
  in_type "zoo_parabs.pool.context" 1
)(in custom zoo_proj
).
Notation "'context_id'" := (
  in_type "zoo_parabs.pool.context" 2
)(in custom zoo_proj
).

Notation "'size'" := (
  in_type "zoo_parabs.pool.t" 0
)(in custom zoo_field
).
Notation "'hub'" := (
  in_type "zoo_parabs.pool.t" 1
)(in custom zoo_field
).
Notation "'domains'" := (
  in_type "zoo_parabs.pool.t" 2
)(in custom zoo_field
).
Notation "'force_mutable'" := (
  in_type "zoo_parabs.pool.t" 3
)(in custom zoo_field
).
