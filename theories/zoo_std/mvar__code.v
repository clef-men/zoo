From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mvar__types.
From zoo Require Import
  options.

Definition mvar_create : val :=
  fun: <> =>
    ref §None.

Definition mvar_make : val :=
  fun: "v" =>
    ref ‘Some( "v" ).

Definition mvar_try_get : val :=
  fun: "t" =>
    !"t".

Definition mvar_is_unset : val :=
  fun: "t" =>
    mvar_try_get "t" == §None.

Definition mvar_is_set : val :=
  fun: "t" =>
    ~ mvar_is_unset "t".

Definition mvar_get : val :=
  fun: "t" =>
    match: mvar_try_get "t" with
    | None =>
        Fail
    | Some "v" =>
        "v"
    end.

Definition mvar_set : val :=
  fun: "t" "v" =>
    "t" <- ‘Some( "v" ).
