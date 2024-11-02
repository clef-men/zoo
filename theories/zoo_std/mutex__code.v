From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mutex__types.
From zoo Require Import
  options.

Definition mutex_create : val :=
  fun: <> =>
    ref #false.

Definition mutex_lock : val :=
  rec: "lock" "t" =>
    if: ~ CAS "t".[contents] #false #true then (
      Yield ;;
      "lock" "t"
    ).

Definition mutex_unlock : val :=
  fun: "t" =>
    "t" <- #false.

Definition mutex_protect : val :=
  fun: "t" "fn" =>
    mutex_lock "t" ;;
    let: "res" := "fn" () in
    mutex_unlock "t" ;;
    "res".
