Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.ws_deque_1.
Require Import zoo_saturn.ws_deque_2__types.
Require Import zoo.options.

Definition ws_deque_2٠create : val :=
  ws_deque_1٠create.

Definition ws_deque_2٠size : val :=
  ws_deque_1٠size.

Definition ws_deque_2٠is_empty : val :=
  ws_deque_1٠is_empty.

Definition ws_deque_2٠push : val :=
  fun: "t" "v" =>
    ws_deque_1٠push "t" (ref "v").

Definition ws_deque_2٠steal : val :=
  fun: "t" =>
    match: ws_deque_1٠steal "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.

Definition ws_deque_2٠pop : val :=
  fun: "t" =>
    match: ws_deque_1٠pop "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.
