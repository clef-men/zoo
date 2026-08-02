Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.clist.
Require Import zoo_std.domain.
Require Import zoo_std.optional.
Require Import zoo.options.

Definition mpmc_stack_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 §clist٠Open.

Definition mpmc_stack_2٠push : val :=
  𝗿𝗲𝗰 "push" "t" "v" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | ⎽ 𝗮𝘀 "old" ->
        𝗹𝗲𝘁 "new_" = ‘clist٠Cons[ "v", "old" ] 𝗶𝗻
        𝗶𝗳 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
          false
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "push" "t" "v"
        )
    𝗲𝗻𝗱.

Definition mpmc_stack_2٠pop : val :=
  𝗿𝗲𝗰 "pop" "t" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        §optional٠Anything
    | clist٠Open ->
        §optional٠Nothing
    | clist٠Cons "v" "new_" 𝗮𝘀 "old" ->
        𝗶𝗳 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
          ‘optional٠Something( "v" )
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "pop" "t"
        )
    𝗲𝗻𝗱.

Definition mpmc_stack_2٠is_closed : val :=
  𝗳𝘂𝗻 "t" ->
    !"t" == §clist٠Closed.

Definition mpmc_stack_2٠close : val :=
  𝗳𝘂𝗻 "t" ->
    𝘅𝗰𝗵𝗴 "t".[contents] §clist٠Closed.
