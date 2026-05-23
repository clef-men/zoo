From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_persistent Require Import
  sstore_2.
From zoo Require Import
  options.

Notation "'Root'" := (
  in_type "zoo_persistent.suf.descr" 0
)(in custom zoo_tag
).
Notation "'Link'" := (
  in_type "zoo_persistent.suf.descr" 1
)(in custom zoo_tag
).
