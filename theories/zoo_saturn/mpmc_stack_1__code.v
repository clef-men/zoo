Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.domain.
Require Import zoo_std.glist.
Require Import zoo_saturn.mpmc_stack_1__types.
Require Import zoo.options.

Definition mpmc_stack_1٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 §Gnil.

Definition mpmc_stack_1٠push : val :=
  𝗿𝗲𝗰 "push" "t" "v" ->
    𝗹𝗲𝘁 "old" = !"t" 𝗶𝗻
    𝗹𝗲𝘁 "new_" = ‘Gcons[ "v", "old" ] 𝗶𝗻
    𝗶𝗳 ~ 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
      domain٠yield () ⍮
      "push" "t" "v"
    ).

Definition mpmc_stack_1٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | Gnil ->
        §None
    | Gcons "v" "new_" 𝗮𝘀 "old" ->
        𝗶𝗳 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
          ‘Some( "v" )
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "t"
        )
    𝗲𝗻𝗱.

Definition mpmc_stack_1٠snapshot : val :=
  𝗳𝘂𝗻 "t" ->
    !"t".
