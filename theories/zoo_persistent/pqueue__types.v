Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo.options.

Notation "'front'" := (
  in_type "zoo_persistent.pqueue.t" 0
)(in custom zoo_proj
).
Notation "'back'" := (
  in_type "zoo_persistent.pqueue.t" 1
)(in custom zoo_proj
).
