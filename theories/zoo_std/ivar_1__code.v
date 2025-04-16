From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  ivar_1__types.
From zoo Require Import
  options.

Definition ivar_1_create : val :=
  fun: <> =>
    ref §None.

Definition ivar_1_try_get : val :=
  fun: "t" =>
    !"t".

Definition ivar_1_is_set : val :=
  fun: "t" =>
    ivar_1_try_get "t" != §None.

Definition ivar_1_get : val :=
  fun: "t" =>
    match: ivar_1_try_get "t" with
    | None =>
        Fail
    | Some "v" =>
        "v"
    end.

Definition ivar_1_set : val :=
  fun: "t" "v" =>
    "t" <- ‘Some( "v" ).
