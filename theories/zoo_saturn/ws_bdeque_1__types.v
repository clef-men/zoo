From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_std Require Import
  array
  domain.
From zoo Require Import
  options.

Notation "'capacity'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 1
)(in custom zoo_field
).
Notation "'front_cache'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 2
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 3
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 4
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_saturn.ws_bdeque_1.t" 5
)(in custom zoo_field
).
