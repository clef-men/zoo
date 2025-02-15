From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'xtchain_next'" := (
  in_type "zoo_std.xtchain.t" 0
)(in custom zoo_field
).
Notation "'xtchain_data'" := (
  in_type "zoo_std.xtchain.t" 1
)(in custom zoo_field
).
