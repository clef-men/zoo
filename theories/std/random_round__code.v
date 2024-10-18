From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  array
  random.
From zoo.std Require Import
  random_round__types.
From zoo Require Import
  options.

Definition random_round_create : val :=
  fun: "sz" =>
    { random_create (), array_unsafe_initi "sz" (fun: "i" => "i"), "sz" }.

Definition random_round_reset : val :=
  fun: "t" =>
    "t" <-{index} array_size "t".{array}.

Definition random_round_next : val :=
  fun: "t" =>
    let: "arr" := "t".{array} in
    let: "i" := "t".{index} in
    let: "j" := random_int "t".{random} "i" in
    let: "res" := array_unsafe_get "arr" "j" in
    let: "i" := "i" - #1 in
    array_unsafe_set "arr" "j" (array_unsafe_get "arr" "i") ;;
    array_unsafe_set "arr" "i" "res" ;;
    "t" <-{index} "i" ;;
    "res".
