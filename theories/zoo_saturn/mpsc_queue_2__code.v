From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  glst
  domain.
From zoo_saturn Require Import
  mpsc_queue_2__types.
From zoo Require Import
  options.

Definition mpsc_queue_2_create : val :=
  fun: <> =>
    { §Gnil, §Gnil }.

Definition mpsc_queue_2_is_empty : val :=
  fun: "t" =>
    match: "t".{front} with
    | Gcons <> <> =>
        #false
    | Gnil =>
        "t".{back} == §Gnil
    end.

Definition mpsc_queue_2_push_front : val :=
  fun: "t" "v" =>
    "t" <-{front} ‘Gcons[ "v", "t".{front} ].

Definition mpsc_queue_2_push_back : val :=
  rec: "push_back" "t" "v" =>
    let: "back" := "t".{back} in
    if: ~ CAS "t".[back] "back" ‘Gcons[ "v", "back" ] then (
      domain_yield () ;;
      "push_back" "t" "v"
    ).

Definition mpsc_queue_2_pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | Gnil =>
        match: glst_rev (Xchg "t".[back] §Gnil) with
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
