Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.glist.
Require Import zoo_std.domain.
Require Import zoo_saturn.mpmc_stack_1__types.
Require Import zoo.options.

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
