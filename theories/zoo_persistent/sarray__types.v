From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo Require Import
  options.

Notation "'Root'" := (
  in_type "zoo_persistent.sarray.descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "zoo_persistent.sarray.descr" 1
)(in custom zoo_tag
).

Notation "'equal'" := (
  in_type "zoo_persistent.sarray.t" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_persistent.sarray.t" 1
)(in custom zoo_field
).
Notation "'root'" := (
  in_type "zoo_persistent.sarray.t" 2
)(in custom zoo_field
).
