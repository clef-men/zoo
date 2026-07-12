Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'Root'" := (
  in_type "zoo_persistent.parray.descr" 0
)(in custom zoo_tag
).
Notation "'Diff'" := (
  in_type "zoo_persistent.parray.descr" 1
)(in custom zoo_tag
).

Notation "'equal'" := (
  in_type "zoo_persistent.parray.descr.Root" 0
)(in custom zoo_proj
).
Notation "'data'" := (
  in_type "zoo_persistent.parray.descr.Root" 1
)(in custom zoo_proj
).
