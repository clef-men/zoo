Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mpsc_flag__types.
Require Import zoo.options.

Definition mpsc_flag٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 false.

Definition mpsc_flag٠get : val :=
  𝗳𝘂𝗻 "1" ->
    !"1".

Definition mpsc_flag٠set : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <- true.
