From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  spsc_waiter.
From unix Require Import
  unix.
From zoo_eio Require Import
  rcfd__types.
From zoo Require Import
  options.

Definition rcfd_make : val :=
  fun: "fd" =>
    { #0, ‘Open@[ "fd" ] }.

Definition rcfd_closed : val :=
  ‘Closing[ fun: <> => () ].

Definition rcfd_put : val :=
  fun: "t" =>
    let: "old" := FAA "t".[ops] #(-1) in
    if: "old" == #1 then (
      match: "t".{state} with
      | Open <> =>
          ()
      | Closing "no_users" as "prev" =>
          if: "t".{ops} ≤ #0 and CAS "t".[state] "prev" rcfd_closed then (
            "no_users" ()
          )
      end
    ).

Definition rcfd_get : val :=
  fun: "t" =>
    FAA "t".[ops] #1 ;;
    match: "t".{state} with
    | Open "fd" =>
        ‘Some( "fd" )
    | Closing <> =>
        rcfd_put "t" ;;
        §None
    end.

Definition rcfd_use : val :=
  fun: "t" "closed" "open_" =>
    match: rcfd_get "t" with
    | None =>
        "closed" ()
    | Some "fd" =>
        let: "res" := "open_" "fd" in
        rcfd_put "t" ;;
        "res"
    end.

Definition rcfd_close : val :=
  fun: "t" =>
    match: "t".{state} with
    | Closing <> =>
        #false
    | Open "fd" as "prev" =>
        let: "close" <> := unix_close "fd" in
        let: "next" := ‘Closing[ "close" ] in
        if: CAS "t".[state] "prev" "next" then (
          if: "t".{ops} == #0 and CAS "t".[state] "next" rcfd_closed then (
            "close" ()
          ) else (
            ()
          ) ;;
          #true
        ) else (
          #false
        )
    end.

Definition rcfd_remove : val :=
  fun: "t" =>
    match: "t".{state} with
    | Closing <> =>
        §None
    | Open "fd" as "prev" =>
        let: "waiter" := spsc_waiter_create () in
        let: "next" :=
          ‘Closing[ fun: <> => spsc_waiter_notify "waiter" ]
        in
        if: CAS "t".[state] "prev" "next" then (
          spsc_waiter_wait "waiter" ;;
          ‘Some( "fd" )
        ) else (
          §None
        )
    end.

Definition rcfd_is_open : val :=
  fun: "t" =>
    match: "t".{state} with
    | Open <> =>
        #true
    | Closing <> =>
        #false
    end.

Definition rcfd_peek : val :=
  fun: "t" =>
    match: "t".{state} with
    | Open "fd" =>
        ‘Some( "fd" )
    | Closing <> =>
        §None
    end.
