From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mvar__types.
From zoo Require Import
  options.

Definition mvar٠create : val :=
  fun: <> =>
    ref §None.

Definition mvar٠make : val :=
  fun: "v" =>
    ref ‘Some( "v" ).

Definition mvar٠try_get : val :=
  fun: "t" =>
    !"t".

Definition mvar٠is_unset : val :=
  fun: "t" =>
    mvar٠try_get "t" == §None.

Definition mvar٠is_set : val :=
  fun: "t" =>
    ~ mvar٠is_unset "t".

Definition mvar٠get : val :=
  fun: "t" =>
    match: mvar٠try_get "t" with
    | None =>
        Fail
    | Some "v" =>
        "v"
    end.

Definition mvar٠set : val :=
  fun: "t" "v" =>
    "t" <- ‘Some( "v" ).
