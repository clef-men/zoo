From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  structeq.
From zoo_std Require Import
  atomic_array
  random
  domain.
From zoo Require Import
  options.

Notation "'Nil'" := (
  in_type "bucket" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "bucket" 1
)(in custom zoo_tag
).
Notation "'Resize'" := (
  in_type "bucket" 2
)(in custom zoo_tag
).

Notation "'bucket'" := (
  in_type "bucket__Resize" 0
)(in custom zoo_field
).

Notation "'Normal'" := (
  in_type "status" 0
)(in custom zoo_tag
).
Notation "'Resizing'" := (
  in_type "status" 1
)(in custom zoo_tag
).

Notation "'resizing_buckets'" := (
  in_type "status__Resizing" 0
)(in custom zoo_proj
).
Notation "'resizing_mask'" := (
  in_type "status__Resizing" 1
)(in custom zoo_proj
).

Notation "'buckets'" := (
  in_type "state" 0
)(in custom zoo_proj
).
Notation "'mask'" := (
  in_type "state" 1
)(in custom zoo_proj
).
Notation "'status'" := (
  in_type "state" 2
)(in custom zoo_proj
).

Notation "'hash'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'equal'" := (
  in_type "t" 1
)(in custom zoo_field
).
Notation "'random'" := (
  in_type "t" 2
)(in custom zoo_field
).
Notation "'sizes'" := (
  in_type "t" 3
)(in custom zoo_field
).
Notation "'state'" := (
  in_type "t" 4
)(in custom zoo_field
).
