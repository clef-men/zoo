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
  fun: "t" "v" =>
    "v" :: "t".

Definition pstack٠pop : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        §None
    | "v" :: "t" =>
        ‘Some( ("v", "t") )
    end.
