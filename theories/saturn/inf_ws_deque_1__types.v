From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier
  inf_array.
From zoo Require Import
  options.

Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "t" 2
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "t" 3
)(in custom zoo_field
).
