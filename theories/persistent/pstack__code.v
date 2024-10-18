From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  lst.
From zoo.persistent Require Import
  pstack__types.
From zoo Require Import
  options.

Definition pstack_empty : val :=
  [].

Definition pstack_is_empty : val :=
  lst_is_empty.

Definition pstack_push : val :=
  fun: "t" "v" =>
    "v" :: "t".

Definition pstack_pop : val :=
  fun: "param" =>
    match: "param" with
    | [] =>
        §None
    | "v" :: "t" =>
        ‘Some( ("v", "t") )
    end.
