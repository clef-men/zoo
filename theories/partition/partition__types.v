From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst.
From zoo Require Import
  options.

Notation "'prev'" := (
  in_type "dllist" 0
)(in custom zoo_field
).
Notation "'next'" := (
  in_type "dllist" 1
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "dllist" 2
)(in custom zoo_field
).
Notation "'class_'" := (
  in_type "dllist" 3
)(in custom zoo_field
).
Notation "'seen'" := (
  in_type "dllist" 4
)(in custom zoo_field
).

Notation "'first'" := (
  in_type "class_" 0
)(in custom zoo_field
).
Notation "'last'" := (
  in_type "class_" 1
)(in custom zoo_field
).
Notation "'len'" := (
  in_type "class_" 2
)(in custom zoo_field
).
Notation "'split'" := (
  in_type "class_" 3
)(in custom zoo_field
).
Notation "'split_len'" := (
  in_type "class_" 4
)(in custom zoo_field
).
