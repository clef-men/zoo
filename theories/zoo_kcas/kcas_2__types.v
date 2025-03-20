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
  in_type "zoo_kcas.kcas_2.state" 0
)(in custom zoo_field
).
Notation "'before'" := (
  in_type "zoo_kcas.kcas_2.state" 1
)(in custom zoo_field
).
Notation "'after'" := (
  in_type "zoo_kcas.kcas_2.state" 2
)(in custom zoo_field
).

Notation "'loc'" := (
  in_type "zoo_kcas.kcas_2.cas" 0
)(in custom zoo_proj
).
Notation "'state'" := (
  in_type "zoo_kcas.kcas_2.cas" 1
)(in custom zoo_proj
).

Notation "'status'" := (
  in_type "zoo_kcas.kcas_2.casn" 0
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "zoo_kcas.kcas_2.casn" 1
)(in custom zoo_field
).

Notation "'Undetermined'" := (
  in_type "zoo_kcas.kcas_2.status" 0
)(in custom zoo_tag
).
Notation "'Before'" := (
  in_type "zoo_kcas.kcas_2.status" 1
)(in custom zoo_tag
).
Notation "'After'" := (
  in_type "zoo_kcas.kcas_2.status" 2
)(in custom zoo_tag
).

Notation "'cmps'" := (
  in_type "zoo_kcas.kcas_2.status.Undetermined" 0
)(in custom zoo_proj
).
Notation "'cass'" := (
  in_type "zoo_kcas.kcas_2.status.Undetermined" 1
)(in custom zoo_proj
).
