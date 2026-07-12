Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_saturn.mpmc_stack_2.
Require Import zoo_std.clist.
Require Import zoo.options.

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
