From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Gnone'" := (
  in_type "zoo_std.goption.t" 0
)(in custom zoo_tag
).
Notation "'Gsome'" := (
  in_type "zoo_std.goption.t" 1
)(in custom zoo_tag
).
