From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_persistent Require Import
  pstore_2.
From zoo Require Import
  options.

Notation "'Root'" := (
  in_type "zoo_persistent.puf.descr" 0
)(in custom zoo_tag
).
Notation "'Link'" := (
  in_type "zoo_persistent.puf.descr" 1
)(in custom zoo_tag
).
