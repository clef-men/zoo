From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  unix
  spsc_waiter.
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
