From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  domain.
From zoo_saturn Require Import
  bag_1__types.
From zoo Require Import
  options.

Definition bag_1_create : val :=
  fun: "sz" =>
    { array_unsafe_init "sz" (fun: <> => ref §None), #0, #0 }.

Definition bag_1_push_0 : val :=
  rec: "push" "slot" "o" =>
    if: ~ CAS "slot".[contents] §None "o" then (
      domain_yield () ;;
      "push" "slot" "o"
    ).

Definition bag_1_push : val :=
  fun: "t" "v" =>
    let: "data" := "t".{data} in
    let: "i" := FAA "t".[back] #1 `rem` array_size "data" in
    bag_1_push_0 (array_unsafe_get "data" "i") ‘Some( "v" ).

Definition bag_1_pop_0 : val :=
  rec: "pop" "slot" =>
    match: !"slot" with
    | None =>
        "pop" "slot"
    | Some "v" as "o" =>
        if: CAS "slot".[contents] "o" §None then (
          "v"
        ) else (
          domain_yield () ;;
          "pop" "slot"
        )
    end.

Definition bag_1_pop : val :=
  fun: "t" =>
    let: "data" := "t".{data} in
    let: "i" := FAA "t".[front] #1 `rem` array_size "data" in
    bag_1_pop_0 (array_unsafe_get "data" "i").
