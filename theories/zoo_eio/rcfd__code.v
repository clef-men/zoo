From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From unix Require Import
  unix.
From zoo_std Require Import
  spsc_waiter.
From zoo_eio Require Import
  rcfd__types.
From zoo Require Import
  options.

Definition rcfd٠make : val :=
  fun: "fd" =>
    { 0, ‘Open@[ "fd" ] }.

Definition rcfd٠closed : val :=
  ‘Closing[ fun: <> => () ].

Definition rcfd٠finish : val :=
  fun: "t" "close" "state" =>
    if: "t".{ops} == 0 and CAS "t".[state] "state" rcfd٠closed then (
      "close" ()
    ).

Definition rcfd٠put : val :=
  fun: "t" =>
    let: "old" := FAA "t".[ops] (-1) in
    if: "old" == 1 then (
      match: "t".{state} with
      | Open <> =>
          ()
      | Closing "close" as "state" =>
          rcfd٠finish "t" "close" "state"
      end
    ).

Definition rcfd٠get : val :=
  fun: "t" =>
    FAA "t".[ops] 1 ;;
    match: "t".{state} with
    | Open "fd" =>
        ‘Some( "fd" )
    | Closing <> =>
        rcfd٠put "t" ;;
        §None
    end.

Definition rcfd٠use : val :=
  fun: "t" "closed" "open_" =>
    match: rcfd٠get "t" with
    | None =>
        "closed" ()
    | Some "fd" =>
        let: "res" := "open_" "fd" in
        rcfd٠put "t" ;;
        "res"
    end.

Definition rcfd٠close : val :=
  fun: "t" =>
    match: "t".{state} with
    | Closing <> =>
        false
    | Open "fd" as "state" =>
        let: "close" <> := unix٠close "fd" in
        let: "new_state" := ‘Closing[ "close" ] in
        if: CAS "t".[state] "state" "new_state" then (
          rcfd٠finish "t" "close" "new_state" ;;
          true
        ) else (
          false
        )
    end.

Definition rcfd٠remove : val :=
  fun: "t" =>
    match: "t".{state} with
    | Closing <> =>
        §None
    | Open "fd" as "state" =>
        let: "waiter" := spsc_waiter٠create () in
        let: "new_state" :=
          ‘Closing[ fun: <> => spsc_waiter٠notify "waiter" ]
        in
        if: CAS "t".[state] "state" "new_state" then (
          spsc_waiter٠wait "waiter" ;;
          ‘Some( "fd" )
        ) else (
          §None
        )
    end.

Definition rcfd٠is_open : val :=
  fun: "t" =>
    match: "t".{state} with
    | Open <> =>
        true
    | Closing <> =>
        false
    end.

Definition rcfd٠peek : val :=
  fun: "t" =>
    match: "t".{state} with
    | Open "fd" =>
        ‘Some( "fd" )
    | Closing <> =>
        §None
    end.
