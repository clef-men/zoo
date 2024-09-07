From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  assert.
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

Notation "'snap_store'" := (
  in_type "snap" 0
)(in custom zoo_proj
).
Notation "'snap_root'" := (
  in_type "snap" 1
)(in custom zoo_proj
).
