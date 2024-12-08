From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition__types.
From zoo Require Import
  options.

Definition condition_create : val :=
  fun: <> =>
    ().

Definition condition_wait : val :=
  fun: "_t" "_mtx" =>
    ().

Definition condition_notify : val :=
  fun: "_t" =>
    ().

Definition condition_notify_all : val :=
  fun: "_t" =>
    ().

Definition condition_wait_until_aux : val :=
  rec: "wait_until_aux" "t" "mtx" "pred" =>
    if: ~ "pred" () then (
      condition_wait "t" "mtx" ;;
      "wait_until_aux" "t" "mtx" "pred"
    ).

Definition condition_wait_until : val :=
  fun: "t" "mtx" "pred" =>
    condition_wait_until_aux "t" "mtx" "pred".

Definition condition_wait_while : val :=
  fun: "t" "mtx" "pred" =>
    condition_wait_until "t" "mtx" (fun: <> => ~ "pred" ()).
