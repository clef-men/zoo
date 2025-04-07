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
      "lock" "t"
    ).

Definition mutex_unlock : val :=
  fun: "t" =>
    "t" <- #false.

Definition mutex_synchronize : val :=
  fun: "t" =>
    mutex_lock "t" ;;
    mutex_unlock "t".

Definition mutex_protect : val :=
  fun: "t" "fn" =>
    mutex_lock "t" ;;
    let: "res" := "fn" () in
    mutex_unlock "t" ;;
    "res".
