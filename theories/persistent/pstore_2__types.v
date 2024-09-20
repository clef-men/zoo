From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  assert.
From zoo Require Import
  options.

Notation "'ref_gen'" := (
  in_type "ref" 0
)(in custom zoo_field
).
Notation "'ref_value'" := (
  in_type "ref" 1
)(in custom zoo_field
).

Notation "'Root'" := (
  in_type "descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "descr" 1
)(in custom zoo_tag
).

Notation "'gen'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'root'" := (
  in_type "t" 1
)(in custom zoo_field
).

Notation "'snap_store'" := (
  in_type "snap" 0
)(in custom zoo_proj
).
Notation "'snap_gen'" := (
  in_type "snap" 1
)(in custom zoo_proj
).
Notation "'snap_root'" := (
  in_type "snap" 2
)(in custom zoo_proj
).
