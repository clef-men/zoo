From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'ClistClosed'" := (
  in_type "zoo_std.clist.t" 0
)(in custom zoo_tag
).
Notation "'ClistOpen'" := (
  in_type "zoo_std.clist.t" 1
)(in custom zoo_tag
).
Notation "'ClistCons'" := (
  in_type "zoo_std.clist.t" 2
)(in custom zoo_tag
).
