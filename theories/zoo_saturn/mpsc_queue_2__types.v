From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  glst
  domain.
From zoo Require Import
  options.

Notation "'front'" := (
  in_type "zoo_saturn.mpsc_queue_2.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.mpsc_queue_2.t" 1
)(in custom zoo_field
).
