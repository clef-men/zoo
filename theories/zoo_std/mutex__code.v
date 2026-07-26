Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex__types.
Require Import zoo.options.

Definition mutex٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 false.

Definition mutex٠lock : val :=
  𝗿𝗲𝗰 "lock" "t" ->
    𝗶𝗳 ~ 𝗰𝗮𝘀 "t".[contents] false true 𝘁𝗵𝗲𝗻 (
      "lock" "t"
    ).

Definition mutex٠create_lock : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 true.

Definition mutex٠unlock : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <- false.

Definition mutex٠synchronize : val :=
  𝗳𝘂𝗻 "t" ->
    mutex٠lock "t" ⍮
    mutex٠unlock "t".

Definition mutex٠protect : val :=
  𝗳𝘂𝗻 "t" "fn" ->
    mutex٠lock "t" ⍮
    𝗹𝗲𝘁 "res" = "fn" () 𝗶𝗻
    mutex٠unlock "t" ⍮
    "res".
