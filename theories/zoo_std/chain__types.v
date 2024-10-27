From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'chain_head'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'chain_tail'" := (
  in_type "t" 1
)(in custom zoo_field
).
