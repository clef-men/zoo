From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  glst
  domain.
From zoo_saturn Require Import
  mpmc_stack_1__types.
From zoo Require Import
  options.

Definition mpmc_stack_1٠create : val :=
  fun: <> =>
    ref §Gnil.

Definition mpmc_stack_1٠push : val :=
  rec: "push" "t" "v" =>
    let: "old" := !"t" in
    let: "new_" := ‘Gcons[ "v", "old" ] in
    if: ~ CAS "t".[contents] "old" "new_" then (
      domain٠yield () ;;
      "push" "t" "v"
    ).

Definition mpmc_stack_1٠pop : val :=
  rec: "pop" "t" =>
    match: !"t" with
    | Gnil =>
        §None
    | Gcons "v" "new_" as "old" =>
        if: CAS "t".[contents] "old" "new_" then (
          ‘Some( "v" )
        ) else (
          domain٠yield () ;;
          "pop" "t"
        )
    end.

Definition mpmc_stack_1٠snapshot : val :=
  fun: "t" =>
    !"t".
