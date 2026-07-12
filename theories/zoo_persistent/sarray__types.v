Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo.options.

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
