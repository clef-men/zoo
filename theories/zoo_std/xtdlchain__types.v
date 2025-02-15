From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'xtdlchain_prev'" := (
  in_type "zoo_std.xtdlchain.t" 0
)(in custom zoo_field
).
Notation "'xtdlchain_next'" := (
  in_type "zoo_std.xtdlchain.t" 1
)(in custom zoo_field
).
Notation "'xtdlchain_data'" := (
  in_type "zoo_std.xtdlchain.t" 2
)(in custom zoo_field
).
