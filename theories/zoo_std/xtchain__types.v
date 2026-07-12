Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'xtchain_next'" := (
  in_type "zoo_std.xtchain.t" 0
)(in custom zoo_field
).
Notation "'xtchain_data'" := (
  in_type "zoo_std.xtchain.t" 1
)(in custom zoo_field
).
