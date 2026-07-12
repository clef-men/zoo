Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.spmc_queue.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'Null'" := (
  in_type "zoo_saturn.bag_2.producers_" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "zoo_saturn.bag_2.producers_" 1
)(in custom zoo_tag
).

Notation "'next'" := (
  in_type "zoo_saturn.bag_2.producers_.Node" 0
)(in custom zoo_field
).
Notation "'queue'" := (
  in_type "zoo_saturn.bag_2.producers_.Node" 1
)(in custom zoo_field
).

Notation "'producer_queue'" := (
  in_type "zoo_saturn.bag_2.producer" 0
)(in custom zoo_proj
).
Notation "'producer_node'" := (
  in_type "zoo_saturn.bag_2.producer" 1
)(in custom zoo_proj
).

Notation "'consumer_queue'" := (
  in_type "zoo_saturn.bag_2.consumer" 0
)(in custom zoo_field
).

Notation "'producers'" := (
  in_type "zoo_saturn.bag_2.t" 0
)(in custom zoo_field
).
