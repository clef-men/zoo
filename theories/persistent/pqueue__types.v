From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Import
  lst.
From zoo Require Import
  options.

Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_proj
).
Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_proj
).
