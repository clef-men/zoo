From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  dynarray_1.
From zoo.std Require Import
  stack__types.
From zoo Require Import
  options.

Definition stack_create : val :=
  dynarray_1_create.

Definition stack_is_empty : val :=
  dynarray_1_is_empty.

Definition stack_push : val :=
  dynarray_1_push.

Definition stack_pop : val :=
  dynarray_1_pop.
