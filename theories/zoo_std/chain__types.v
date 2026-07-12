Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'chain_next'" := (
  in_type "zoo_std.chain.t" 0
)(in custom zoo_field
).
Notation "'chain_data'" := (
  in_type "zoo_std.chain.t" 1
)(in custom zoo_field
).
