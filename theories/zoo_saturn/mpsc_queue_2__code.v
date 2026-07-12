Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.glist.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpsc_queue_2__types.
Require Import zoo.options.

Definition mpsc_queue_2٠create : val :=
  fun: <> =>
    { §Gnil, §Gnil }.

Definition mpsc_queue_2٠is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | Gcons <> <> =>
        false
    | Gnil =>
        "t".{back} == §Gnil
    end.

Definition mpsc_queue_2٠push_front : val :=
  fun: "t" "v" =>
    "t" <-{front} ‘Gcons[ "v", "t".{front} ].

Definition mpsc_queue_2٠push_back : val :=
  rec: "push_back" "t" "v" =>
    let: "back" := "t".{back} in
    if: ~ CAS "t".[back] "back" ‘Gcons[ "v", "back" ] then (
      domain٠yield () ;;
      "push_back" "t" "v"
    ).

Definition mpsc_queue_2٠pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | Gnil =>
        match: glist٠rev (Xchg "t".[back] §Gnil) with
        | Gnil =>
            §None
        | Gcons "v" "front" =>
            "t" <-{front} "front" ;;
            ‘Some( "v" )
        end
    | Gcons "v" "front" =>
        "t" <-{front} "front" ;;
        ‘Some( "v" )
    end.
