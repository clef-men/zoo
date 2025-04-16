From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  ivar_3__types.
From zoo Require Import
  options.

Definition ivar_3_create : val :=
  fun: <> =>
    ref ‘Unset[ [] ].

Definition ivar_3_is_set : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        #false
    | Set <> =>
        #true
    end.

Definition ivar_3_try_get : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        §None
    | Set "v" =>
        ‘Some( "v" )
    end.

Definition ivar_3_get : val :=
  fun: "t" =>
    match: !"t" with
    | Unset <> =>
        Fail
    | Set "v" =>
        "v"
    end.

Definition ivar_3_wait : val :=
  rec: "wait" "t" "waiter" =>
    match: !"t" with
    | Unset "waiters" =>
        if:
          CAS
            "t".[contents]
            ‘Unset[ "waiters" ]
            ‘Unset[ "waiter" :: "waiters" ]
        then (
          §None
        ) else (
          "wait" "t" "waiter"
        )
    | Set "v" =>
        ‘Some( "v" )
    end.

Definition ivar_3_set : val :=
  fun: "t" "v" =>
    match: Xchg "t".[contents] ‘Set( "v" ) with
    | Set <> =>
        Fail
    | Unset "waiters" =>
        "waiters"
    end.
