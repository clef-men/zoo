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

Notation "'next_split'" := (
  in_type "block" 0
)(in custom zoo_field
).
Notation "'first'" := (
  in_type "block" 1
)(in custom zoo_field
).
Notation "'last'" := (
  in_type "block" 2
)(in custom zoo_field
).
Notation "'len'" := (
  in_type "block" 3
)(in custom zoo_field
).
Notation "'split_start'" := (
  in_type "block" 4
)(in custom zoo_field
).
Notation "'split_len'" := (
  in_type "block" 5
)(in custom zoo_field
).

Notation "'blocks_head'" := (
  in_type "t" 0
)(in custom zoo_field
).
