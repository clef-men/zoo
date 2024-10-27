From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'Nothing'" := (
  in_type "t" 0
)(in custom zoo_tag
).
Notation "'Anything'" := (
  in_type "t" 1
)(in custom zoo_tag
).
Notation "'Something'" := (
  in_type "t" 2
)(in custom zoo_tag
).
