From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst.
From zoo_persistent Require Import
  pstack__types.
From zoo Require Import
  options.

Definition pstack٠empty : val :=
  [].

Definition pstack٠is_empty : val :=
  lst٠is_empty.

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
