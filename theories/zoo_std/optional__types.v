From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Nothing'" := (
  in_type "zoo_std.optional.t" 0
)(in custom zoo_tag
).
Notation "'Anything'" := (
  in_type "zoo_std.optional.t" 1
)(in custom zoo_tag
).
Notation "'Something'" := (
  in_type "zoo_std.optional.t" 2
)(in custom zoo_tag
).
