From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Gnil'" := (
  in_type "zoo_std.glst.t" 0
)(in custom zoo_tag
).
Notation "'Gcons'" := (
  in_type "zoo_std.glst.t" 1
)(in custom zoo_tag
).
