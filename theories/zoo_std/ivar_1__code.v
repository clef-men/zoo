From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  ivar_1__types.
From zoo Require Import
  options.

Definition ivar_1٠create : val :=
  fun: <> =>
    ref §None.

Definition ivar_1٠make : val :=
  fun: "v" =>
    ref ‘Some( "v" ).

Definition ivar_1٠try_get : val :=
  fun: "t" =>
    !"t".

Definition ivar_1٠is_unset : val :=
  fun: "t" =>
    ivar_1٠try_get "t" == §None.

Definition ivar_1٠is_set : val :=
  fun: "t" =>
    ~ ivar_1٠is_unset "t".

Definition ivar_1٠get : val :=
  fun: "t" =>
    match: ivar_1٠try_get "t" with
    | None =>
        Fail
    | Some "v" =>
        "v"
    end.

Definition ivar_1٠set : val :=
  fun: "t" "v" =>
    "t" <- ‘Some( "v" ).
