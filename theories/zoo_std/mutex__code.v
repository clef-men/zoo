Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.mutex__types.
Require Import zoo.options.

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
