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
  in_type "state" 0
)(in custom zoo_field
).
Notation "'before'" := (
  in_type "state" 1
)(in custom zoo_field
).
Notation "'after'" := (
  in_type "state" 2
)(in custom zoo_field
).

Notation "'loc'" := (
  in_type "cas" 0
)(in custom zoo_proj
).
Notation "'state'" := (
  in_type "cas" 1
)(in custom zoo_proj
).

Notation "'cmps'" := (
  in_type "casn" 0
)(in custom zoo_field
).
Notation "'status'" := (
  in_type "casn" 1
)(in custom zoo_field
).
Notation "'proph'" := (
  in_type "casn" 2
)(in custom zoo_field
).

Notation "'Undetermined'" := (
  in_type "status" 0
)(in custom zoo_tag
).
Notation "'Before'" := (
  in_type "status" 1
)(in custom zoo_tag
).
Notation "'After'" := (
  in_type "status" 2
)(in custom zoo_tag
).
