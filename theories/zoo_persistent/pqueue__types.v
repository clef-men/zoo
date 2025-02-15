From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst.
From zoo Require Import
  options.

Notation "'front'" := (
  in_type "zoo_persistent.pqueue.t" 0
)(in custom zoo_proj
).
Notation "'back'" := (
  in_type "zoo_persistent.pqueue.t" 1
)(in custom zoo_proj
).
