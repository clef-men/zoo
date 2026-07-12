Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.array.
Require Import zoo_std.random_state.
Require Import zoo_std.random_round__types.
Require Import zoo.options.

Definition random_round٠create : val :=
  fun: "sz" =>
    { random_state٠create (),
      array٠unsafe_initi "sz" (fun: "i" => "i"),
      "sz"
    }.

Definition random_round٠reset : val :=
  fun: "t" =>
    "t" <-{index} array٠size "t".{array}.

Definition random_round٠next : val :=
  fun: "t" =>
    let: "arr" := "t".{array} in
    let: "i" := "t".{index} in
    let: "j" := random_state٠int "t".{random} "i" in
    let: "res" := array٠unsafe_get "arr" "j" in
    let: "i" := "i" - 1 in
    array٠unsafe_set "arr" "j" (array٠unsafe_get "arr" "i") ;;
    array٠unsafe_set "arr" "i" "res" ;;
    "t" <-{index} "i" ;;
    "res".
