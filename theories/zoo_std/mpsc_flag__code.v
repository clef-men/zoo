From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mpsc_flag__types.
From zoo Require Import
  options.

Definition mpsc_flag_create : val :=
  fun: <> =>
    ref false.

Definition mpsc_flag_get : val :=
  fun: "1" =>
    !"1".

Definition mpsc_flag_set : val :=
  fun: "t" =>
    "t" <- true.
