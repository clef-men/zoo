From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst.
From zoo_saturn Require Import
  mpmc_stack_2.
From zoo_parabs Require Import
  pool.
From zoo Require Import
  options.

Notation "'task'" := (
  in_type "zoo_parabs.vertex.t" 0
)(in custom zoo_field
).
Notation "'preds'" := (
  in_type "zoo_parabs.vertex.t" 1
)(in custom zoo_field
).
Notation "'succs'" := (
  in_type "zoo_parabs.vertex.t" 2
)(in custom zoo_field
).
