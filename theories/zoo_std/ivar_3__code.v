From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  ivar_3__types.
From zoo Require Import
  options.

Definition ivar_3٠create : val :=
  fun: <> =>
    ref ‘Unset[ [] ].

Definition ivar_3٠make : val :=
  fun: "v" =>
    ref ‘Set( "v" ).

Definition ivar_3٠is_unset : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        true
    | Set <> =>
        false
    end.

Definition ivar_3٠is_set : val :=
  fun: "t" =>
    ~ ivar_3٠is_unset "t".

Definition ivar_3٠try_get : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        §None
    | Set "v" =>
        ‘Some( "v" )
    end.

Definition ivar_3٠get : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        Fail
    | Set "v" =>
        "v"
    end.

Definition ivar_3٠wait : val :=
  rec: "wait" "t" "waiter" =>
    match: !"t" with
    | Unset "waiters" as "state" =>
        if:
          CAS "t".[contents] "state" ‘Unset[ "waiter" :: "waiters" ]
        then (
          §None
        ) else (
          "wait" "t" "waiter"
        )
    | Set "v" =>
        ‘Some( "v" )
    end.

Definition ivar_3٠set : val :=
  fun: "t" "v" =>
    match: Xchg "t".[contents] ‘Set( "v" ) with
    | Set <> =>
        Fail
    | Unset "waiters" =>
        "waiters"
    end.
