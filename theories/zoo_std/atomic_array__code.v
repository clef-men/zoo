From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo_std Require Import
  atomic_array__types.
From zoo Require Import
  options.

Definition atomic_array_make : val :=
  array_make.

Definition atomic_array_init : val :=
  array_init.

Definition atomic_array_initi : val :=
  array_initi.

Definition atomic_array_size : val :=
  array_size.

Definition atomic_array_unsafe_get : val :=
  array_unsafe_get.

Definition atomic_array_get : val :=
  array_get.

Definition atomic_array_unsafe_set : val :=
  array_unsafe_set.

Definition atomic_array_set : val :=
  array_set.

Definition atomic_array_unsafe_xchg : val :=
  array_unsafe_xchg.

Definition atomic_array_unsafe_cas : val :=
  array_unsafe_cas.

Definition atomic_array_unsafe_faa : val :=
  array_unsafe_faa.
