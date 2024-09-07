From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  mutex
  condition.
From zoo Require Import
  options.

Notation "'result'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'mutex'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'condition'" := (
  in_type "t" 2
)(in custom zoo_field
).
