From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  lst.
From zoo.saturn Require Import
  mpsc_queue_2__types.
From zoo Require Import
  options.

Definition mpsc_queue_2_create : val :=
  fun: <> =>
    { §Nil, §Nil }.

Definition mpsc_queue_2_push : val :=
  rec: "push" "t" "v" =>
    let: "back" := "t".{back} in
    ifnot: CAS "t".[back] "back" ‘Cons( "v", "back" ) then (
      Yield ;;
      "push" "t" "v"
    ).

Definition mpsc_queue_2_pop : val :=
  fun: "t" =>
    match: "t".{front} with
    | Nil =>
        match: lst_rev (Xchg "t".[back] §Nil) with
        | Nil =>
            §None
        | Cons "v" "front" =>
            "t" <-{front} "front" ;;
            ‘Some( "v" )
        end
    | Cons "v" "front" =>
        "t" <-{front} "front" ;;
        ‘Some( "v" )
    end.
