From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  random
  array.
From zoo Require Import
  options.

Notation "'Nil'" := (
  in_type "bucket" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "bucket" 1
)(in custom zoo_tag
).

Notation "'hash'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'equal'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'buckets'" := (
  in_type "t" 2
)(in custom zoo_field
).
Notation "'mask'" := (
  in_type "t" 3
)(in custom zoo_field
).
Notation "'size'" := (
  in_type "t" 4
)(in custom zoo_field
).
