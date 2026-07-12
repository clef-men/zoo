Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.chain.
Require Import zoo.options.

Notation "'front'" := (
  in_type "zoo_std.queue_1.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_std.queue_1.t" 1
)(in custom zoo_field
).
