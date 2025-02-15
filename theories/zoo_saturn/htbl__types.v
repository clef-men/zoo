From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  atomic_array
  random
  domain.
From zoo Require Import
  options.

Notation "'Init'" := (
  in_type "zoo_saturn.htbl.bucket" 0
)(in custom zoo_tag
).
Notation "'Nil'" := (
  in_type "zoo_saturn.htbl.bucket" 1
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "zoo_saturn.htbl.bucket" 2
)(in custom zoo_tag
).
Notation "'Resize'" := (
  in_type "zoo_saturn.htbl.bucket" 3
)(in custom zoo_tag
).

Notation "'Normal'" := (
  in_type "zoo_saturn.htbl.status" 0
)(in custom zoo_tag
).
Notation "'Resizing'" := (
  in_type "zoo_saturn.htbl.status" 1
)(in custom zoo_tag
).

Notation "'resizing_buckets'" := (
  in_type "zoo_saturn.htbl.status__Resizing" 0
)(in custom zoo_proj
).
Notation "'resizing_mask'" := (
  in_type "zoo_saturn.htbl.status__Resizing" 1
)(in custom zoo_proj
).

Notation "'buckets'" := (
  in_type "zoo_saturn.htbl.state" 0
)(in custom zoo_proj
).
Notation "'mask'" := (
  in_type "zoo_saturn.htbl.state" 1
)(in custom zoo_proj
).
Notation "'status'" := (
  in_type "zoo_saturn.htbl.state" 2
)(in custom zoo_proj
).

Notation "'hash'" := (
  in_type "zoo_saturn.htbl.t" 0
)(in custom zoo_field
).
Notation "'equal'" := (
  in_type "zoo_saturn.htbl.t" 1
)(in custom zoo_field
).
Notation "'sizes'" := (
  in_type "zoo_saturn.htbl.t" 2
)(in custom zoo_field
).
Notation "'state'" := (
  in_type "zoo_saturn.htbl.t" 3
)(in custom zoo_field
).
