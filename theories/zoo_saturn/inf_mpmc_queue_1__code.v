From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  inf_array
  int
  optional
  domain.
From zoo_saturn Require Import
  inf_mpmc_queue_1__types.
From zoo Require Import
  options.

Definition inf_mpmc_queue_1_create : val :=
  fun: <> =>
    { inf_array_create §Nothing, #0, #0 }.

Definition inf_mpmc_queue_1_size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "proph" := Proph in
    let: "back" := "t".{back} in
    if: Resolve "t".{front} "proph" () == "front" then (
      int_positive_part ("back" - "front")
    ) else (
      "size" "t"
    ).

Definition inf_mpmc_queue_1_is_empty : val :=
  fun: "t" =>
    inf_mpmc_queue_1_size "t" == #0.

Definition inf_mpmc_queue_1_push : val :=
  fun: "t" "v" =>
    let: "i" := FAA "t".[back] #1 in
    inf_array_set "t".{data} "i" ‘Something( "v" ).

Definition inf_mpmc_queue_1_pop_0 : val :=
  rec: "pop" "t" "i" =>
    match: inf_array_get "t".{data} "i" with
    | Nothing =>
        domain_yield () ;;
        "pop" "t" "i"
    | Anything =>
        Fail
    | Something "v" =>
        inf_array_set "t".{data} "i" §Anything ;;
        "v"
    end.

Definition inf_mpmc_queue_1_pop : val :=
  fun: "t" =>
    let: "i" := FAA "t".[front] #1 in
    inf_mpmc_queue_1_pop_0 "t" "i".
