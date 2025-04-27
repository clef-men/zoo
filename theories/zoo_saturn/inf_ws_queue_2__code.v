From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_saturn Require Import
  inf_ws_queue_1.
From zoo_saturn Require Import
  inf_ws_queue_2__types.
From zoo Require Import
  options.

Definition inf_ws_queue_2_create : val :=
  inf_ws_queue_1_create.

Definition inf_ws_queue_2_push : val :=
  fun: "t" "v" =>
    inf_ws_queue_1_push "t" (ref "v").

Definition inf_ws_queue_2_steal : val :=
  fun: "t" =>
    match: inf_ws_queue_1_steal "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.

Definition inf_ws_queue_2_pop : val :=
  fun: "t" =>
    match: inf_ws_queue_1_pop "t" with
    | None =>
        §None
    | Some "slot" =>
        ‘Some( !"slot" )
    end.
