Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.glist__types.
Require Import zoo.options.

Definition glist٠rev_app : val :=
  𝗿𝗲𝗰 "rev_app" "t1" "t2" ->
    𝗺𝗮𝘁𝗰𝗵 "t1" 𝘄𝗶𝘁𝗵
    | Gnil ->
        "t2"
    | Gcons "v" "t1" ->
        "rev_app" "t1" ‘Gcons[ "v", "t2" ]
    𝗲𝗻𝗱.

Definition glist٠rev : val :=
  𝗳𝘂𝗻 "t" ->
    glist٠rev_app "t" §Gnil.
