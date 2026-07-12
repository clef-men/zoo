Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

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
