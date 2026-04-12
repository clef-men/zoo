From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo Require Import
  options.

Notation "'mutex'" := (
  in_type "zoo_parabs.waiter.t" 0
)(in custom zoo_field
).
Notation "'condition'" := (
  in_type "zoo_parabs.waiter.t" 1
)(in custom zoo_field
).
Notation "'flag'" := (
  in_type "zoo_parabs.waiter.t" 2
)(in custom zoo_field
).
