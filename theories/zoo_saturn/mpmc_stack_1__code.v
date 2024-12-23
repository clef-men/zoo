From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_stack_1__types.
From zoo Require Import
  options.

Definition mpmc_stack_1_create : val :=
  fun: <> =>
    ref [].

Definition mpmc_stack_1_push : val :=
  rec: "push" "t" "v" =>
    let: "old" := !"t" in
    let: "new_" := "v" :: "old" in
    if: ~ CAS "t".[contents] "old" "new_" then (
      domain_yield () ;;
      "push" "t" "v"
    ).

Definition mpmc_stack_1_pop : val :=
  rec: "pop" "t" =>
    match: !"t" with
    | [] =>
        §None
    | "v" :: "new_" as "old" =>
        if: CAS "t".[contents] "old" "new_" then (
          ‘Some( "v" )
        ) else (
          domain_yield () ;;
          "pop" "t"
        )
    end.
