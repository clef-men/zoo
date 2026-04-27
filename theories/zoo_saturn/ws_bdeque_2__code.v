From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_saturn Require Import
  ws_bdeque_1.
From zoo_saturn Require Import
  ws_bdeque_2__types.
From zoo Require Import
  options.

Definition ws_bdeque_2٠create : val :=
  ws_bdeque_1٠create.

Definition ws_bdeque_2٠capacity : val :=
  ws_bdeque_1٠capacity.

Definition ws_bdeque_2٠size : val :=
  ws_bdeque_1٠size.

Definition ws_bdeque_2٠is_empty : val :=
  ws_bdeque_1٠is_empty.

Definition ws_bdeque_2٠push : val :=
  fun: "t" "v" =>
    ws_bdeque_1٠push "t" (ref "v").

Definition ws_bdeque_2٠steal : val :=
  fun: "t" =>
    match: ws_bdeque_1٠steal "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.

Definition ws_bdeque_2٠pop : val :=
  fun: "t" =>
    match: ws_bdeque_1٠pop "t" with
    | None =>
        §None
    | Some "slot" =>
        let: "v" := !"slot" in
        "slot" <- () ;;
        ‘Some( "v" )
    end.
