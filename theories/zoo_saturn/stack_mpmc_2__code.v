Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import backoff.backoff.
Require Import zoo_std.clist.
Require Import zoo_std.optional.
Require Import zoo.options.

Definition stack_mpmc_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    𝗿𝗲𝗳 §clist٠Open.

Definition stack_mpmc_2٠push₁ : val :=
  𝗿𝗲𝗰 "push" "t" "v" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        true
    | ⎽ 𝗮𝘀 "old" ->
        𝗹𝗲𝘁 "new_" = ‘clist٠Cons[ "v", "old" ] 𝗶𝗻
        𝗶𝗳 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
          false
        ) 𝗲𝗹𝘀𝗲 (
          "push" "t" "v" (backoff٠once "backoff")
        )
    𝗲𝗻𝗱.

Definition stack_mpmc_2٠push : val :=
  𝗳𝘂𝗻 "t" "v" ->
    stack_mpmc_2٠push₁ "t" "v" backoff٠default.

Definition stack_mpmc_2٠pop₁ : val :=
  𝗿𝗲𝗰 "pop" "t" "backoff" ->
    𝗺𝗮𝘁𝗰𝗵 !"t" 𝘄𝗶𝘁𝗵
    | clist٠Closed ->
        §optional٠Anything
    | clist٠Open ->
        §optional٠Nothing
    | clist٠Cons "v" "new_" 𝗮𝘀 "old" ->
        𝗶𝗳 𝗰𝗮𝘀 "t".[contents] "old" "new_" 𝘁𝗵𝗲𝗻 (
          ‘optional٠Something( "v" )
        ) 𝗲𝗹𝘀𝗲 (
          "pop" "t" (backoff٠once "backoff")
        )
    𝗲𝗻𝗱.

Definition stack_mpmc_2٠pop : val :=
  𝗳𝘂𝗻 "t" ->
    stack_mpmc_2٠pop₁ "t" backoff٠default.

Definition stack_mpmc_2٠is_closed : val :=
  𝗳𝘂𝗻 "t" ->
    !"t" == §clist٠Closed.

Definition stack_mpmc_2٠close : val :=
  𝗳𝘂𝗻 "t" ->
    𝘅𝗰𝗵𝗴 "t".[contents] §clist٠Closed.
