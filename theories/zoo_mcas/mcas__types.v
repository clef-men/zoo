From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  list.
From zoo Require Import
  identifier.
From zoo Require Import
  options.

Notation "'casn'" := (
  in_type "zoo_mcas.mcas.state" 0
)(in custom zoo_field
).
Notation "'before'" := (
  in_type "zoo_mcas.mcas.state" 1
)(in custom zoo_field
).
Notation "'after'" := (
  in_type "zoo_mcas.mcas.state" 2
)(in custom zoo_field
).

Notation "'loc'" := (
  in_type "zoo_mcas.mcas.cas" 0
)(in custom zoo_proj
).
Notation "'state'" := (
  in_type "zoo_mcas.mcas.cas" 1
)(in custom zoo_proj
).

Notation "'status'" := (
  in_type "zoo_mcas.mcas.casn" 0
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_mcas.mcas.casn" 1
)(in custom zoo_field
).

Notation "'Undetermined'" := (
  in_type "zoo_mcas.mcas.status" 0
)(in custom zoo_tag
).
Notation "'Before'" := (
  in_type "zoo_mcas.mcas.status" 1
)(in custom zoo_tag
).
Notation "'After'" := (
  in_type "zoo_mcas.mcas.status" 2
)(in custom zoo_tag
).
