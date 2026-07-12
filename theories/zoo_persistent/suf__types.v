Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_persistent.sstore_2.
Require Import zoo.options.

Notation "'Root'" := (
  in_type "zoo_persistent.suf.descr" 0
)(in custom zoo_tag
).
Notation "'Link'" := (
  in_type "zoo_persistent.suf.descr" 1
)(in custom zoo_tag
).
