From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_saturn Require Import
  ws_deque_1.
From zoo_saturn Require Import
  ws_deque_2__types.
From zoo Require Import
  options.

Definition ws_deque_2_create : val :=
  ws_deque_1_create.

Definition ws_deque_2_size : val :=
  ws_deque_1_size.

Definition ws_deque_2_is_empty : val :=
  ws_deque_1_is_empty.

Definition ws_deque_2_push : val :=
  fun: "t" "v" =>
    ws_deque_1_push "t" (ref "v").

Definition ws_deque_2_steal : val :=
  fun: "t" =>
    match: ws_deque_1_steal "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.

Definition ws_deque_2_pop : val :=
  fun: "t" =>
    match: ws_deque_1_pop "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.
