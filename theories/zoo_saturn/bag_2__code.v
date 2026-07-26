Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.spmc_queue.
Require Import zoo_std.domain.
Require Import zoo_saturn.bag_2__types.
Require Import zoo.options.

Definition bag_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §Null }.

Definition bag_2٠add_producer₀ : val :=
  𝗿𝗲𝗰 "add_producer" "t" "queue" ->
    𝗹𝗲𝘁 "producers" = "t".{producers} 𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵 ‘Node{ "producers", "queue" } 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "new_producers" ->
        𝗶𝗳
          𝗰𝗮𝘀 "t".[producers] "producers" "new_producers"
        𝘁𝗵𝗲𝗻 (
          "new_producers"
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "add_producer" "t" "queue"
        )
    𝗲𝗻𝗱.

Definition bag_2٠add_producer : val :=
  𝗳𝘂𝗻 "t" "queue" ->
    bag_2٠add_producer₀ "t" ‘Some( "queue" ).

Definition bag_2٠create_producer : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "queue" = spmc_queue٠create () 𝗶𝗻
    𝗹𝗲𝘁 "node" = bag_2٠add_producer "t" "queue" 𝗶𝗻
    ("queue", "node").

Definition bag_2٠close_producer : val :=
  𝗳𝘂𝗻 "producer" ->
    𝗺𝗮𝘁𝗰𝗵 "producer".<producer_node> 𝘄𝗶𝘁𝗵
    | Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        "node_r" <-{queue} §None
    𝗲𝗻𝗱.

Definition bag_2٠create_consumer : val :=
  𝗳𝘂𝗻 "_t" ->
    { §None }.

Definition bag_2٠push : val :=
  𝗳𝘂𝗻 "producer" "v" ->
    spmc_queue٠push "producer".<producer_queue> "v".

Definition bag_2٠pop₀ : val :=
  𝗿𝗲𝗰 "pop" "consumer" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | Null ->
        §None
    | Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        𝗺𝗮𝘁𝗰𝗵 "node_r".{queue} 𝘄𝗶𝘁𝗵
        | None ->
            "pop" "consumer" "node_r".{next}
        | Some "queue" ->
            𝗺𝗮𝘁𝗰𝗵 spmc_queue٠pop "queue" 𝘄𝗶𝘁𝗵
            | None ->
                "pop" "consumer" "node_r".{next}
            | Some ⎽ 𝗮𝘀 "res" ->
                "consumer" <-{consumer_queue} ‘Some( "queue" ) ⍮
                "res"
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition bag_2٠pop₁ : val :=
  𝗳𝘂𝗻 "t" "consumer" ->
    bag_2٠pop₀ "consumer" "t".{producers}.

Definition bag_2٠pop : val :=
  𝗳𝘂𝗻 "t" "consumer" ->
    𝗺𝗮𝘁𝗰𝗵 "consumer".{consumer_queue} 𝘄𝗶𝘁𝗵
    | None ->
        bag_2٠pop₁ "t" "consumer"
    | Some "queue" ->
        𝗺𝗮𝘁𝗰𝗵 spmc_queue٠pop "queue" 𝘄𝗶𝘁𝗵
        | None ->
            bag_2٠pop₁ "t" "consumer"
        | Some ⎽ 𝗮𝘀 "res" ->
            "res"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
