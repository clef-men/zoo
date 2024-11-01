From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  spsc_waiter.
From unix Require Import
  unix.
From zoo Require Import
  options.

Notation "'Open'" := (
  in_type "state" 0
)(in custom zoo_tag
).
Notation "'Closing'" := (
  in_type "state" 1
)(in custom zoo_tag
).

Notation "'ops'" := (
  in_type "t" 0
)(in custom zoo_field
).
Notation "'state'" := (
  in_type "t" 1
)(in custom zoo_field
).
