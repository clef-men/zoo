Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.int__types.
Require Import zoo.options.

Definition int٠min : val :=
  𝗳𝘂𝗻 "n1" "n2" ->
    𝗶𝗳 "n1" < "n2" 𝘁𝗵𝗲𝗻 (
      "n1"
    ) 𝗲𝗹𝘀𝗲 (
      "n2"
    ).

Definition int٠max : val :=
  𝗳𝘂𝗻 "n1" "n2" ->
    𝗶𝗳 "n1" < "n2" 𝘁𝗵𝗲𝗻 (
      "n2"
    ) 𝗲𝗹𝘀𝗲 (
      "n1"
    ).

Definition int٠positive_part : val :=
  𝗳𝘂𝗻 "t" ->
    int٠max 0 "t".
