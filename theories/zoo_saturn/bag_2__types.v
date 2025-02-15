From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  spmc_queue.
From zoo Require Import
  options.

Notation "'Null'" := (
  in_type "zoo_saturn.bag_2.producers_" 0
)(in custom zoo_tag
).
Notation "'Node'" := (
  in_type "zoo_saturn.bag_2.producers_" 1
)(in custom zoo_tag
).

Notation "'next'" := (
  in_type "zoo_saturn.bag_2.producers___Node" 0
)(in custom zoo_field
).
Notation "'queue'" := (
  in_type "zoo_saturn.bag_2.producers___Node" 1
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
