From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assert.
From zoo Require Import
  options.

Notation "'Root'" := (
  in_type "zoo_persistent.pstore_1.descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "zoo_persistent.pstore_1.descr" 1
)(in custom zoo_tag
).

Notation "'snapshot_store'" := (
  in_type "zoo_persistent.pstore_1.snapshot" 0
)(in custom zoo_proj
).
Notation "'snapshot_root'" := (
  in_type "zoo_persistent.pstore_1.snapshot" 1
)(in custom zoo_proj
).
