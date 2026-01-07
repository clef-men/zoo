From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst
  domain.
From zoo_saturn Require Import
  mpsc_queue_3__types.
From zoo Require Import
  options.

Definition mpsc_queue_3_create : val :=
  fun: <> =>
    { §ClstOpen, §ClstOpen }.

Definition mpsc_queue_3_is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | ClstClosed =>
        true
    | ClstCons <> <> =>
        false
    | ClstOpen =>
        match: "t".{back} with
        | ClstCons <> <> =>
            false
        |_ =>
            true
        end
    end.

Definition mpsc_queue_3_push_front : val :=
  fun: "t" "v" =>
    match: "t".{front} with
    | ClstClosed =>
        true
    |_ as "front" =>
        "t" <-{front} ‘ClstCons[ "v", "front" ] ;;
        false
    end.

Definition mpsc_queue_3_push_back : val :=
  rec: "push_back" "t" "v" =>
    match: "t".{back} with
    | ClstClosed =>
        true
    |_ as "back" =>
        if: CAS "t".[back] "back" ‘ClstCons[ "v", "back" ] then (
          false
        ) else (
          domain_yield () ;;
          "push_back" "t" "v"
        )
    end.

Definition mpsc_queue_3_pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | ClstClosed =>
        §None
    | ClstCons "v" "front" =>
        "t" <-{front} "front" ;;
        ‘Some( "v" )
    | ClstOpen =>
        match: Xchg "t".[back] §ClstOpen with
        | ClstOpen =>
            §None
        |_ as "back" =>
            match: clst_rev_app "back" §ClstOpen with
            | ClstCons "v" "front" =>
                "t" <-{front} "front" ;;
                ‘Some( "v" )
            |_ =>
                Fail
            end
        end
    end.

Definition mpsc_queue_3_close : val :=
  fun: "t" =>
    match: Xchg "t".[back] §ClstClosed with
    | ClstClosed =>
        true
    |_ as "back" =>
        "t" <-{front} clst_app "t".{front} (clst_rev_app "back" §ClstClosed) ;;
        false
    end.
