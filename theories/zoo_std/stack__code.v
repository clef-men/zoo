From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  dynarray_1.
From zoo_std Require Import
  stack__types.
From zoo Require Import
  options.

Definition stack٠create : val :=
  dynarray_1٠create.

Definition stack٠is_empty : val :=
  dynarray_1٠is_empty.

Definition stack٠push : val :=
  dynarray_1٠push.

Definition stack٠pop : val :=
  dynarray_1٠pop.
