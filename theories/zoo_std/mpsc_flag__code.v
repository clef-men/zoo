Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mpsc_flag__types.
Require Import zoo.options.

Definition mpsc_flag٠create : val :=
  fun: <> =>
    ref false.

Definition mpsc_flag٠get : val :=
  fun: "1" =>
    !"1".

Definition mpsc_flag٠set : val :=
  fun: "t" =>
    "t" <- true.
