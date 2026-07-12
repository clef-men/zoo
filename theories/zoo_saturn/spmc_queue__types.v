Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'Null'" := (
  in_type "zoo_saturn.spmc_queue.node" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "zoo_saturn.spmc_queue.node" 1
)(in custom zoo_tag
).

Notation "'next'" := (
  in_type "zoo_saturn.spmc_queue.node.Node" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.spmc_queue.node.Node" 1
)(in custom zoo_field
).

Notation "'front'" := (
  in_type "zoo_saturn.spmc_queue.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.spmc_queue.t" 1
)(in custom zoo_field
).
