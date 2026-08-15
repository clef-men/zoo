Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Export backoff.backoff.
Require Export zoo_std.clist.
Require Import zoo.options.

Notation "'front'" := (
  in_type "zoo_saturn.queue_mpsc_3.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.queue_mpsc_3.t" 1
)(in custom zoo_field
).
