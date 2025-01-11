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
  inf_mpmc_queue_2__types.
From zoo Require Import
  options.

Definition inf_mpmc_queue_2_create : val :=
  fun: <> =>
    { inf_array_create §Nothing, #0, #0 }.

Definition inf_mpmc_queue_2_size : val :=
  rec: "size" "t" =>
    let: "front" := "t".{front} in
    let: "proph" := Proph in
    let: "back" := "t".{back} in
    if: Resolve "t".{front} "proph" () != "front" then (
      "size" "t"
    ) else (
      int_positive_part ("back" - "front")
    ).

Definition inf_mpmc_queue_2_is_empty : val :=
  fun: "t" =>
    inf_mpmc_queue_2_size "t" == #0.

Definition inf_mpmc_queue_2_push : val :=
  rec: "push" "t" "v" =>
    let: "i" := FAA "t".[back] #1 in
    if: ~ inf_array_cas "t".{data} "i" §Nothing ‘Something( "v" ) then (
      "push" "t" "v"
    ).

Definition inf_mpmc_queue_2_pop : val :=
  rec: "pop" "t" =>
    let: "i" := FAA "t".[front] #1 in
    match: inf_array_xchg "t".{data} "i" §Anything with
    | Nothing =>
        domain_yield () ;;
        "pop" "t"
    | Anything =>
        Fail
    | Something "v" =>
        inf_array_set "t".{data} "i" §Anything ;;
        "v"
    end.
