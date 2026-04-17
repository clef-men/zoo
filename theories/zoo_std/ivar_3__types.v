From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Unset'" := (
  in_type "zoo_std.ivar_3.state" 0
)(in custom zoo_tag
).
Notation "'Set'" := (
  in_type "zoo_std.ivar_3.state" 1
)(in custom zoo_tag
).
