From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'xdlchain_prev'" := (
  in_type "zoo_std.xdlchain.t" 0
)(in custom zoo_field
).
Notation "'xdlchain_next'" := (
  in_type "zoo_std.xdlchain.t" 1
)(in custom zoo_field
).
Notation "'xdlchain_data'" := (
  in_type "zoo_std.xdlchain.t" 2
)(in custom zoo_field
).
