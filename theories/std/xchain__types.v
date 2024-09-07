From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Notation "'xchain_next'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'xchain_data'" := (
  in_type "t" 1
)(in custom zoo_field
).
