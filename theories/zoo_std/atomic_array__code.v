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

Definition atomic_array٠make : val :=
  array٠make.

Definition atomic_array٠init : val :=
  array٠init.

Definition atomic_array٠initi : val :=
  array٠initi.

Definition atomic_array٠size : val :=
  array٠size.

Definition atomic_array٠unsafe_get : val :=
  array٠unsafe_get.

Definition atomic_array٠get : val :=
  array٠get.

Definition atomic_array٠unsafe_set : val :=
  array٠unsafe_set.

Definition atomic_array٠set : val :=
  array٠set.

Definition atomic_array٠unsafe_xchg : val :=
  array٠unsafe_xchg.

Definition atomic_array٠unsafe_cas : val :=
  array٠unsafe_cas.

Definition atomic_array٠unsafe_faa : val :=
  array٠unsafe_faa.

Definition atomic_array٠foldli : val :=
  array٠foldli.

Definition atomic_array٠foldl : val :=
  array٠foldl.

Definition atomic_array٠sum : val :=
  array٠sum.
