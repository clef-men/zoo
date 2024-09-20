From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo Require Import
  inf_ws_deque_1.
From zoo.saturn Require Import
  inf_ws_deque_2__types.
From zoo Require Import
  options.

Definition inf_ws_deque_2_create : val :=
  fun: <> =>
    inf_ws_deque_1_create ().

Definition inf_ws_deque_2_push : val :=
  fun: "t" "v" =>
    inf_ws_deque_1_push "t" (ref "v").

Definition inf_ws_deque_2_steal : val :=
  fun: "t" =>
    match: inf_ws_deque_1_steal "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.

Definition inf_ws_deque_2_pop : val :=
  fun: "t" =>
    match: inf_ws_deque_1_pop "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.
