From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  random_state.
From zoo_std Require Import
  random_round__types.
From zoo Require Import
  options.

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
