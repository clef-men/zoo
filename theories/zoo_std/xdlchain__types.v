Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Notation "'prev'" := (
  in_type "zoo_std.xdlchain.t" 0
)(in custom zoo_field
).
Notation "'next'" := (
  in_type "zoo_std.xdlchain.t" 1
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_std.xdlchain.t" 2
)(in custom zoo_field
).
