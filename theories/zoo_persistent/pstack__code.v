Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.list.
Require Import zoo_persistent.pstack__types.
Require Import zoo.options.

Definition pstack٠empty : val :=
  [].

Definition pstack٠is_empty : val :=
  list٠is_empty.

Definition pstack٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    "v" :: "t".

Definition pstack٠pop : val :=
  𝗳𝘂𝗻 "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | [] ->
        §None
    | "v" :: "t" ->
        ‘Some( ("v", "t") )
    𝗲𝗻𝗱.
