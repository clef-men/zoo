From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  random_state.
From zoo Require Import
  options.

Notation "'random'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'array'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'index'" := (
  in_type "t" 2
)(in custom zoo_field
).
