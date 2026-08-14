Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Export zoo_std.domain.
Require Export zoo_std.glist.
Require Import zoo.options.

Notation "'front'" := (
  in_type "zoo_saturn.queue_mpsc_2.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.queue_mpsc_2.t" 1
)(in custom zoo_field
).
