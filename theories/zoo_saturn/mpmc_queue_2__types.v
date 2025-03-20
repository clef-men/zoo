From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo Require Import
  options.

Notation "'Front'" := (
  in_type "zoo_saturn.mpmc_queue_2.front" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "zoo_saturn.mpmc_queue_2.front" 1
)(in custom zoo_tag
).

Notation "'Back'" := (
  in_type "zoo_saturn.mpmc_queue_2.back" 0
)(in custom zoo_tag
).
Notation "'Snoc'" := (
  in_type "zoo_saturn.mpmc_queue_2.back" 1
)(in custom zoo_tag
).
Notation "'Used'" := (
  in_type "zoo_saturn.mpmc_queue_2.back" 2
)(in custom zoo_tag
).

Notation "'index'" := (
  in_type "zoo_saturn.mpmc_queue_2.back.Back" 0
)(in custom zoo_field
).
Notation "'move'" := (
  in_type "zoo_saturn.mpmc_queue_2.back.Back" 1
)(in custom zoo_field
).

Notation "'front'" := (
  in_type "zoo_saturn.mpmc_queue_2.t" 0
)(in custom zoo_field
).
Notation "'back'" := (
  in_type "zoo_saturn.mpmc_queue_2.t" 1
)(in custom zoo_field
).
