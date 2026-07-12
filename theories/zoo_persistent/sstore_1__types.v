Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assert.
Require Import zoo.options.

Notation "'Root'" := (
  in_type "zoo_persistent.sstore_1.descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "zoo_persistent.sstore_1.descr" 1
)(in custom zoo_tag
).

Notation "'snapshot_store'" := (
  in_type "zoo_persistent.sstore_1.snapshot" 0
)(in custom zoo_proj
).
Notation "'snapshot_root'" := (
  in_type "zoo_persistent.sstore_1.snapshot" 1
)(in custom zoo_proj
).
