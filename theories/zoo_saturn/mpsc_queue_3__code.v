Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpsc_queue_3__types.
Require Import zoo.options.

Definition mpsc_queue_3٠create : val :=
  fun: <> =>
    { §ClistOpen, §ClistOpen }.

Definition mpsc_queue_3٠is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | ClistClosed =>
        true
    | ClistCons <> <> =>
        false
    | ClistOpen =>
        match: "t".{back} with
        | ClistCons <> <> =>
            false
        |_ =>
            true
        end
    end.

Definition mpsc_queue_3٠push_front : val :=
  fun: "t" "v" =>
    match: "t".{front} with
    | ClistClosed =>
        true
    |_ as "front" =>
        "t" <-{front} ‘ClistCons[ "v", "front" ] ;;
        false
    end.

Definition mpsc_queue_3٠push_back : val :=
  rec: "push_back" "t" "v" =>
    match: "t".{back} with
    | ClistClosed =>
        true
    |_ as "back" =>
        if: CAS "t".[back] "back" ‘ClistCons[ "v", "back" ] then (
          false
        ) else (
          domain٠yield () ;;
          "push_back" "t" "v"
        )
    end.

Definition mpsc_queue_3٠pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | ClistClosed =>
        §None
    | ClistCons "v" "front" =>
        "t" <-{front} "front" ;;
        ‘Some( "v" )
    | ClistOpen =>
        match: Xchg "t".[back] §ClistOpen with
        | ClistOpen =>
            §None
        |_ as "back" =>
            match: clist٠rev_app "back" §ClistOpen with
            | ClistCons "v" "front" =>
                "t" <-{front} "front" ;;
                ‘Some( "v" )
            |_ =>
                Fail
            end
        end
    end.

Definition mpsc_queue_3٠close : val :=
  fun: "t" =>
    match: Xchg "t".[back] §ClistClosed with
    | ClistClosed =>
        true
    |_ as "back" =>
        "t" <-{front}
          clist٠app "t".{front} (clist٠rev_app "back" §ClistClosed) ;;
        false
    end.
