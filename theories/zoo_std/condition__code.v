Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.options.

Definition condition٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    ().

Definition condition٠notify : val :=
  𝗳𝘂𝗻 "_t" ->
    ().

Definition condition٠notify_all : val :=
  𝗳𝘂𝗻 "_t" ->
    ().

Definition condition٠wait : val :=
  𝗳𝘂𝗻 "_t" "_mtx" ->
    ().

Definition condition٠wait_until : val :=
  𝗿𝗲𝗰 "wait_until" "t" "mtx" "pred" ->
    𝗶𝗳 ~ "pred" () 𝘁𝗵𝗲𝗻 (
      condition٠wait "t" "mtx" ⍮
      "wait_until" "t" "mtx" "pred"
    ).

Definition condition٠wait_while : val :=
  𝗳𝘂𝗻 "t" "mtx" "pred" ->
    condition٠wait_until "t" "mtx" (𝗳𝘂𝗻 ⎽ -> ~ "pred" ()).
