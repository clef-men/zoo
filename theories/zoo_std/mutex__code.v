From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex__types.
From zoo Require Import
  options.

Definition mutex٠create : val :=
  fun: <> =>
    ref false.

Definition mutex٠lock : val :=
  rec: "lock" "t" =>
    if: ~ CAS "t".[contents] false true then (
      "lock" "t"
    ).

Definition mutex٠create_lock : val :=
  fun: <> =>
    ref true.

Definition mutex٠unlock : val :=
  fun: "t" =>
    "t" <- false.

Definition mutex٠synchronize : val :=
  fun: "t" =>
    mutex٠lock "t" ;;
    mutex٠unlock "t".

Definition mutex٠protect : val :=
  fun: "t" "fn" =>
    mutex٠lock "t" ;;
    let: "res" := "fn" () in
    mutex٠unlock "t" ;;
    "res".
