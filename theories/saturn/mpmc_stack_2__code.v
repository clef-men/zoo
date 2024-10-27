From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst
  optional.
From saturn Require Import
  mpmc_stack_2__types.
From zoo Require Import
  options.

Definition mpmc_stack_2_create : val :=
  fun: <> =>
    ref §ClstOpen.

Definition mpmc_stack_2_push : val :=
  rec: "push" "t" "v" =>
    match: !"t" with
    | ClstClosed =>
        #true
    |_ as "old" =>
        let: "new_" := ‘ClstCons( "v", "old" ) in
        if: CAS "t".[contents] "old" "new_" then (
          #false
        ) else (
          Yield ;;
          "push" "t" "v"
        )
    end.

Definition mpmc_stack_2_pop : val :=
  rec: "pop" "t" =>
    match: !"t" with
    | ClstClosed =>
        §Anything
    | ClstOpen =>
        §Nothing
    | ClstCons "v" "new_" as "old" =>
        if: CAS "t".[contents] "old" "new_" then (
          ‘Something( "v" )
        ) else (
          Yield ;;
          "pop" "t"
        )
    end.

Definition mpmc_stack_2_is_closed : val :=
  fun: "t" =>
    !"t" == §ClstClosed.

Definition mpmc_stack_2_close : val :=
  fun: "t" =>
    Xchg "t".[contents] §ClstClosed.
