Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo.program_logic.identifier.
Require Import zoo.options.

Notation "'front'" := (
  in_type "zoo_saturn.ws_deque_1.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.ws_deque_1.t" 1
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.ws_deque_1.t" 2
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_saturn.ws_deque_1.t" 3
)(in custom zoo_field
).
