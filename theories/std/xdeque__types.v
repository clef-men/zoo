From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Notation "'xdeque_prev'" := (
  in_type "node" 0
)(in custom zoo_field
).
Notation "'xdeque_next'" := (
  in_type "node" 1
)(in custom zoo_field
).
Notation "'xdeque_data'" := (
  in_type "node" 2
)(in custom zoo_field
).
