Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.inf_ws_deque_1.
Require Import zoo_saturn.inf_ws_deque_2__types.
Require Import zoo.options.

Definition inf_ws_deque_2٠create : val :=
  inf_ws_deque_1٠create.

Definition inf_ws_deque_2٠size : val :=
  inf_ws_deque_1٠size.

Definition inf_ws_deque_2٠is_empty : val :=
  inf_ws_deque_1٠is_empty.

Definition inf_ws_deque_2٠push : val :=
  fun: "t" "v" =>
    inf_ws_deque_1٠push "t" (ref "v").

Definition inf_ws_deque_2٠steal : val :=
  fun: "t" =>
    match: inf_ws_deque_1٠steal "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.

Definition inf_ws_deque_2٠pop : val :=
  fun: "t" =>
    match: inf_ws_deque_1٠pop "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.
