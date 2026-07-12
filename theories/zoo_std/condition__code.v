Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition__types.
Require Import zoo.options.

Definition condition٠create : val :=
  fun: <> =>
    ().

Definition condition٠notify : val :=
  fun: "_t" =>
    ().

Definition condition٠notify_all : val :=
  fun: "_t" =>
    ().

Definition condition٠wait : val :=
  fun: "_t" "_mtx" =>
    ().

Definition condition٠wait_until : val :=
  rec: "wait_until" "t" "mtx" "pred" =>
    if: ~ "pred" () then (
      condition٠wait "t" "mtx" ;;
      "wait_until" "t" "mtx" "pred"
    ).

Definition condition٠wait_while : val :=
  fun: "t" "mtx" "pred" =>
    condition٠wait_until "t" "mtx" (fun: <> => ~ "pred" ()).
