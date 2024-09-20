From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  int
  array
  mutex.
From zoo Require Import
  options.

Notation "'data'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'default'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'mutex'" := (
  in_type "t" 2
)(in custom zoo_field
).
