Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.queue_spmc.
Require Import zoo_std.domain.
Require Import zoo.options.

Notation "'bag_2٠Null'" := (
  in_type "zoo_saturn.bag_2.producers_" 0
)(in custom zoo_tag
).
Notation "'bag_2٠Node'" := (
  in_type "zoo_saturn.bag_2.producers_" 1
)(in custom zoo_tag
).

Notation "'bag_2٠next'" := (
  in_type "zoo_saturn.bag_2.producers_.Node" 0
)(in custom zoo_field
).
Notation "'bag_2٠queue'" := (
  in_type "zoo_saturn.bag_2.producers_.Node" 1
)(in custom zoo_field
).

Notation "'bag_2٠producer_queue'" := (
  in_type "zoo_saturn.bag_2.producer" 0
)(in custom zoo_proj
).
Notation "'bag_2٠producer_node'" := (
  in_type "zoo_saturn.bag_2.producer" 1
)(in custom zoo_proj
).

Notation "'bag_2٠consumer_queue'" := (
  in_type "zoo_saturn.bag_2.consumer" 0
)(in custom zoo_field
).

Notation "'bag_2٠producers'" := (
  in_type "zoo_saturn.bag_2.t" 0
)(in custom zoo_field
).

Definition bag_2٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    { §bag_2٠Null }.

Definition bag_2٠add_producer₁ : val :=
  𝗿𝗲𝗰 "add_producer" "t" "queue" ->
    𝗹𝗲𝘁 "producers" = "t".{bag_2٠producers} 𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵
      ‘bag_2٠Node{ "producers", "queue" }
    𝘄𝗶𝘁𝗵
    | bag_2٠Node ⎽ ⎽ 𝗮𝘀 "new_producers" ->
        𝗶𝗳
          𝗰𝗮𝘀 "t".[bag_2٠producers] "producers" "new_producers"
        𝘁𝗵𝗲𝗻 (
          "new_producers"
        ) 𝗲𝗹𝘀𝗲 (
          domain٠yield () ⍮
          "add_producer" "t" "queue"
        )
    𝗲𝗻𝗱.

Definition bag_2٠add_producer : val :=
  𝗳𝘂𝗻 "t" "queue" ->
    bag_2٠add_producer₁ "t" ‘Some( "queue" ).

Definition bag_2٠create_producer : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "queue" = queue_spmc٠create () 𝗶𝗻
    𝗹𝗲𝘁 "node" = bag_2٠add_producer "t" "queue" 𝗶𝗻
    ("queue", "node").

Definition bag_2٠close_producer : val :=
  𝗳𝘂𝗻 "producer" ->
    𝗺𝗮𝘁𝗰𝗵 "producer".<bag_2٠producer_node> 𝘄𝗶𝘁𝗵
    | bag_2٠Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        "node_r" <-{bag_2٠queue} §None
    𝗲𝗻𝗱.

Definition bag_2٠create_consumer : val :=
  𝗳𝘂𝗻 "_t" ->
    { §None }.

Definition bag_2٠push : val :=
  𝗳𝘂𝗻 "producer" "v" ->
    queue_spmc٠push "producer".<bag_2٠producer_queue> "v".

Definition bag_2٠pop₂ : val :=
  𝗿𝗲𝗰 "pop" "consumer" "param" ->
    𝗺𝗮𝘁𝗰𝗵 "param" 𝘄𝗶𝘁𝗵
    | bag_2٠Null ->
        §None
    | bag_2٠Node ⎽ ⎽ 𝗮𝘀 "node_r" ->
        𝗺𝗮𝘁𝗰𝗵 "node_r".{bag_2٠queue} 𝘄𝗶𝘁𝗵
        | None ->
            "pop" "consumer" "node_r".{bag_2٠next}
        | Some "queue" ->
            𝗺𝗮𝘁𝗰𝗵 queue_spmc٠pop "queue" 𝘄𝗶𝘁𝗵
            | None ->
                "pop" "consumer" "node_r".{bag_2٠next}
            | Some ⎽ 𝗮𝘀 "res" ->
                "consumer" <-{bag_2٠consumer_queue} ‘Some( "queue" ) ⍮
                "res"
            𝗲𝗻𝗱
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition bag_2٠pop₁ : val :=
  𝗳𝘂𝗻 "t" "consumer" ->
    bag_2٠pop₂ "consumer" "t".{bag_2٠producers}.

Definition bag_2٠pop : val :=
  𝗳𝘂𝗻 "t" "consumer" ->
    𝗺𝗮𝘁𝗰𝗵 "consumer".{bag_2٠consumer_queue} 𝘄𝗶𝘁𝗵
    | None ->
        bag_2٠pop₁ "t" "consumer"
    | Some "queue" ->
        𝗺𝗮𝘁𝗰𝗵 queue_spmc٠pop "queue" 𝘄𝗶𝘁𝗵
        | None ->
            bag_2٠pop₁ "t" "consumer"
        | Some ⎽ 𝗮𝘀 "res" ->
            "res"
        𝗲𝗻𝗱
    𝗲𝗻𝗱.
