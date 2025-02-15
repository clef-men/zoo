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
  in_type "zoo_partition.partition.elt" 0
)(in custom zoo_field
).
Notation "'next'" := (
  in_type "zoo_partition.partition.elt" 1
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_partition.partition.elt" 2
)(in custom zoo_field
).
Notation "'class_'" := (
  in_type "zoo_partition.partition.elt" 3
)(in custom zoo_field
).
Notation "'seen'" := (
  in_type "zoo_partition.partition.elt" 4
)(in custom zoo_field
).

Notation "'first'" := (
  in_type "zoo_partition.partition.class_" 0
)(in custom zoo_field
).
Notation "'last'" := (
  in_type "zoo_partition.partition.class_" 1
)(in custom zoo_field
).
Notation "'len'" := (
  in_type "zoo_partition.partition.class_" 2
)(in custom zoo_field
).
Notation "'split'" := (
  in_type "zoo_partition.partition.class_" 3
)(in custom zoo_field
).
Notation "'split_len'" := (
  in_type "zoo_partition.partition.class_" 4
)(in custom zoo_field
).
