From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  options.

Notation "'xdeque_prev'" := (
  in_type "zoo_std.xdeque.node" 0
)(in custom zoo_field
).
Notation "'xdeque_next'" := (
  in_type "zoo_std.xdeque.node" 1
)(in custom zoo_field
).
Notation "'xdeque_data'" := (
  in_type "zoo_std.xdeque.node" 2
)(in custom zoo_field
).
