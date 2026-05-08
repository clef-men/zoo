From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clist
  optional
  domain.
From zoo_saturn Require Import
  mpmc_stack_2__types.
From zoo Require Import
  options.

Definition mpmc_stack_2٠create : val :=
  fun: <> =>
    ref §ClistOpen.

Definition mpmc_stack_2٠push : val :=
  rec: "push" "t" "v" =>
    match: !"t" with
    | ClistClosed =>
        true
    |_ as "old" =>
        let: "new_" := ‘ClistCons[ "v", "old" ] in
        if: CAS "t".[contents] "old" "new_" then (
          false
        ) else (
          domain٠yield () ;;
          "push" "t" "v"
        )
    end.

Definition mpmc_stack_2٠pop : val :=
  rec: "pop" "t" =>
    match: !"t" with
    | ClistClosed =>
        §Anything
    | ClistOpen =>
        §Nothing
    | ClistCons "v" "new_" as "old" =>
        if: CAS "t".[contents] "old" "new_" then (
          ‘Something( "v" )
        ) else (
          domain٠yield () ;;
          "pop" "t"
        )
    end.

Definition mpmc_stack_2٠is_closed : val :=
  fun: "t" =>
    !"t" == §ClistClosed.

Definition mpmc_stack_2٠close : val :=
  fun: "t" =>
    Xchg "t".[contents] §ClistClosed.
