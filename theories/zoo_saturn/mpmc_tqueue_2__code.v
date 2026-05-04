From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  atomic_array
  optional.
From zoo_saturn Require Import
  mpmc_tqueue_2__types.
From zoo Require Import
  options.

Definition mpmc_tqueue_2٠create : val :=
  fun: "cap" =>
    let: "data" := atomic_array٠make "cap" §Nothing in
    { "cap", "data", 0, 0 }.

Definition mpmc_tqueue_2٠make : val :=
  fun: "cap" "v" =>
    let: "data" := atomic_array٠make "cap" §Nothing in
    atomic_array٠unsafe_set "data" 0 ‘Something( "v" ) ;;
    { "cap", "data", 0, 1 }.

Definition mpmc_tqueue_2٠is_empty : val :=
  fun: "t" =>
    let: "front" := "t".{front} in
    let: "back" := "t".{back} in
    "back" ≤ "front".

Definition mpmc_tqueue_2٠push₀ : val :=
  rec: "push" "t" "v" =>
    let: "i" := FAA "t".[back] 1 in
    if: "t".{capacity} ≤ "i" then (
      false
    ) else if:
       atomic_array٠unsafe_cas "t".{data} "i" §Nothing ‘Something( "v" )
     then (
      true
    ) else (
      "push" "t" "v"
    ).

Definition mpmc_tqueue_2٠push : val :=
  fun: "t" "v" =>
    if: "t".{capacity} ≤ "t".{back} then (
      false
    ) else (
      mpmc_tqueue_2٠push₀ "t" "v"
    ).

Definition mpmc_tqueue_2٠pop : val :=
  fun: "t" =>
    if: "t".{capacity} ≤ "t".{front} then (
      §Anything
    ) else (
      let: "i" := FAA "t".[front] 1 in
      if: "t".{capacity} ≤ "i" then (
        §Anything
      ) else (
        atomic_array٠unsafe_xchg "t".{data} "i" §Anything
      )
    ).
