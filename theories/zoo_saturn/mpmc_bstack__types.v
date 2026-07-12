Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'Nil'" := (
  in_type "zoo_saturn.mpmc_bstack.list" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "zoo_saturn.mpmc_bstack.list" 1
)(in custom zoo_tag
).

Notation "'capacity'" := (
  in_type "zoo_saturn.mpmc_bstack.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.mpmc_bstack.t" 1
)(in custom zoo_field
).
