From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'ClstClosed'" := (
  in_type "zoo_std.clst.t" 0
)(in custom zoo_tag
).
Notation "'ClstOpen'" := (
  in_type "zoo_std.clst.t" 1
)(in custom zoo_tag
).
Notation "'ClstCons'" := (
  in_type "zoo_std.clst.t" 2
)(in custom zoo_tag
).
