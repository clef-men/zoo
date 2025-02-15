From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_std Require Import
  lst.
From zoo Require Import
  options.

Notation "'casn'" := (
  in_type "zoo_kcas.kcas_1.state" 0
)(in custom zoo_field
).
Notation "'before'" := (
  in_type "zoo_kcas.kcas_1.state" 1
)(in custom zoo_field
).
Notation "'after'" := (
  in_type "zoo_kcas.kcas_1.state" 2
)(in custom zoo_field
).

Notation "'loc'" := (
  in_type "zoo_kcas.kcas_1.cas" 0
)(in custom zoo_proj
).
Notation "'state'" := (
  in_type "zoo_kcas.kcas_1.cas" 1
)(in custom zoo_proj
).

Notation "'status'" := (
  in_type "zoo_kcas.kcas_1.casn" 0
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_kcas.kcas_1.casn" 1
)(in custom zoo_field
).

Notation "'Undetermined'" := (
  in_type "zoo_kcas.kcas_1.status" 0
)(in custom zoo_tag
).
Notation "'Before'" := (
  in_type "zoo_kcas.kcas_1.status" 1
)(in custom zoo_tag
).
Notation "'After'" := (
  in_type "zoo_kcas.kcas_1.status" 2
)(in custom zoo_tag
).

Notation "'cass'" := (
  in_type "zoo_kcas.kcas_1.status__Undetermined" 0
)(in custom zoo_proj
).
