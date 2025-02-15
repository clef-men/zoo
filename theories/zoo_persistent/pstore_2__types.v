From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  assert.
From zoo Require Import
  options.

Notation "'ref_gen'" := (
  in_type "zoo_persistent.pstore_2.ref" 0
)(in custom zoo_field
).
Notation "'ref_value'" := (
  in_type "zoo_persistent.pstore_2.ref" 1
)(in custom zoo_field
).

Notation "'Root'" := (
  in_type "zoo_persistent.pstore_2.descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "zoo_persistent.pstore_2.descr" 1
)(in custom zoo_tag
).

Notation "'gen'" := (
  in_type "zoo_persistent.pstore_2.t" 0
)(in custom zoo_field
).
Notation "'root'" := (
  in_type "zoo_persistent.pstore_2.t" 1
)(in custom zoo_field
).

Notation "'snap_store'" := (
  in_type "zoo_persistent.pstore_2.snap" 0
)(in custom zoo_proj
).
Notation "'snap_gen'" := (
  in_type "zoo_persistent.pstore_2.snap" 1
)(in custom zoo_proj
).
Notation "'snap_root'" := (
  in_type "zoo_persistent.pstore_2.snap" 2
)(in custom zoo_proj
).
