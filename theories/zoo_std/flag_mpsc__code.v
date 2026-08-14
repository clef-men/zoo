Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Definition flag_mpsc٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 false.

Definition flag_mpsc٠get : val :=
  𝗳𝘂𝗻 "1" ->
    !"1".

Definition flag_mpsc٠set : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <- true.
