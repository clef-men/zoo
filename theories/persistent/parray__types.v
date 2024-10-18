From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  array.
From zoo Require Import
  options.

Notation "'Root'" := (
  in_type "descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "descr" 1
)(in custom zoo_tag
).
