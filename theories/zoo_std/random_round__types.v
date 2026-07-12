Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.random_state.
Require Import zoo.options.

Notation "'random'" := (
  in_type "zoo_std.random_round.t" 0
)(in custom zoo_field
).
Notation "'array'" := (
  in_type "zoo_std.random_round.t" 1
)(in custom zoo_field
).
Notation "'index'" := (
  in_type "zoo_std.random_round.t" 2
)(in custom zoo_field
).
