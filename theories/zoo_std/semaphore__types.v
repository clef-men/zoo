Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo.options.

Notation "'mutex'" := (
  in_type "zoo_std.semaphore.t" 0
)(in custom zoo_field
).
Notation "'condition'" := (
  in_type "zoo_std.semaphore.t" 1
)(in custom zoo_field
).
Notation "'count'" := (
  in_type "zoo_std.semaphore.t" 2
)(in custom zoo_field
).
