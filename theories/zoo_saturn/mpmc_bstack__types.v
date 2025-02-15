From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Nil'" := (
  in_type "zoo_saturn.mpmc_bstack.lst" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "zoo_saturn.mpmc_bstack.lst" 1
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
