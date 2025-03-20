From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Null'" := (
  in_type "zoo_saturn.mpmc_queue_1.node" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "zoo_saturn.mpmc_queue_1.node" 1
)(in custom zoo_tag
).

Notation "'next'" := (
  in_type "zoo_saturn.mpmc_queue_1.node.Node" 0
)(in custom zoo_field
).
Notation "'data'" := (
  in_type "zoo_saturn.mpmc_queue_1.node.Node" 1
)(in custom zoo_field
).

Notation "'front'" := (
  in_type "zoo_saturn.mpmc_queue_1.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.mpmc_queue_1.t" 1
)(in custom zoo_field
).
