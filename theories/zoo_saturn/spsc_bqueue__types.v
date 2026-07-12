Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo.options.

Notation "'data'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 0
)(in custom zoo_field
).
Notation "'front'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 1
)(in custom zoo_field
).
Notation "'front_cache'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 2
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 3
)(in custom zoo_field
).
Notation "'back_cache'" := (
  in_type "zoo_saturn.spsc_bqueue.t" 4
)(in custom zoo_field
).
