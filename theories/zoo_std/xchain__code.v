Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'xchain٠next'" := (
  in_type "zoo_std.xchain.t" 0
)(in custom zoo_field
).
Notation "'xchain٠data'" := (
  in_type "zoo_std.xchain.t" 1
)(in custom zoo_field
).
