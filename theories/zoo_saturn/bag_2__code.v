Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_saturn.spmc_queue.
Require Import zoo_std.domain.
Require Import zoo_saturn.bag_2__types.
Require Import zoo.options.

Definition bag_2٠create : val :=
  fun: <> =>
    { §Null }.

Definition bag_2٠add_producer₀ : val :=
  rec: "add_producer" "t" "queue" =>
    let: "producers" := "t".{producers} in
    match: ‘Node{ "producers", "queue" } with
    | Node <> <> as "new_producers" =>
        if: CAS "t".[producers] "producers" "new_producers" then (
          "new_producers"
        ) else (
          domain٠yield () ;;
          "add_producer" "t" "queue"
        )
    end.

Definition bag_2٠add_producer : val :=
  fun: "t" "queue" =>
    bag_2٠add_producer₀ "t" ‘Some( "queue" ).

Definition bag_2٠create_producer : val :=
  fun: "t" =>
    let: "queue" := spmc_queue٠create () in
    let: "node" := bag_2٠add_producer "t" "queue" in
    ("queue", "node").

Definition bag_2٠close_producer : val :=
  fun: "producer" =>
    match: "producer".<producer_node> with
    | Node <> <> as "node_r" =>
        "node_r" <-{queue} §None
    end.

Definition bag_2٠create_consumer : val :=
  fun: "_t" =>
    { §None }.

Definition bag_2٠push : val :=
  fun: "producer" "v" =>
    spmc_queue٠push "producer".<producer_queue> "v".

Definition bag_2٠pop₀ : val :=
  rec: "pop" "consumer" "param" =>
    match: "param" with
    | Null =>
        §None
    | Node <> <> as "node_r" =>
        match: "node_r".{queue} with
        | None =>
            "pop" "consumer" "node_r".{next}
        | Some "queue" =>
            match: spmc_queue٠pop "queue" with
            | None =>
                "pop" "consumer" "node_r".{next}
            | Some <> as "res" =>
                "consumer" <-{consumer_queue} ‘Some( "queue" ) ;;
                "res"
            end
        end
    end.

Definition bag_2٠pop₁ : val :=
  fun: "t" "consumer" =>
    bag_2٠pop₀ "consumer" "t".{producers}.

Definition bag_2٠pop : val :=
  fun: "t" "consumer" =>
    match: "consumer".{consumer_queue} with
    | None =>
        bag_2٠pop₁ "t" "consumer"
    | Some "queue" =>
        match: spmc_queue٠pop "queue" with
        | None =>
            bag_2٠pop₁ "t" "consumer"
        | Some <> as "res" =>
            "res"
        end
    end.
