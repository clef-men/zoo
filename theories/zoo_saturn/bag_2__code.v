From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  spmc_queue.
From zoo_saturn Require Import
  bag_2__types.
From zoo Require Import
  options.

Definition bag_2_create : val :=
  fun: <> =>
    { §Null }.

Definition bag_2_add_producer_0 : val :=
  rec: "add_producer" "t" "queue" =>
    let: "producers" := "t".{producers} in
    match: ‘Node{ "producers", "queue" } with
    | Node <> <> as "new_producers" =>
        if: CAS "t".[producers] "producers" "new_producers" then (
          "new_producers"
        ) else (
          domain_yield () ;;
          "add_producer" "t" "queue"
        )
    end.

Definition bag_2_add_producer : val :=
  fun: "t" "queue" =>
    bag_2_add_producer_0 "t" ‘Some( "queue" ).

Definition bag_2_create_producer : val :=
  fun: "t" =>
    let: "queue" := spmc_queue_create () in
    let: "node" := bag_2_add_producer "t" "queue" in
    ("queue", "node").

Definition bag_2_close_producer : val :=
  fun: "producer" =>
    match: "producer".<producer_node> with
    | Node <> <> as "node_r" =>
        "node_r" <-{queue} §None
    end.

Definition bag_2_create_consumer : val :=
  fun: "_t" =>
    { §None }.

Definition bag_2_push : val :=
  fun: "producer" "v" =>
    spmc_queue_push "producer".<producer_queue> "v".

Definition bag_2_pop_0 : val :=
  rec: "pop" "consumer" "param" =>
    match: "param" with
    | Null =>
        §None
    | Node <> <> as "node_r" =>
        match: "node_r".{queue} with
        | None =>
            "pop" "consumer" "node_r".{next}
        | Some "queue" =>
            match: spmc_queue_pop "queue" with
            | None =>
                "pop" "consumer" "node_r".{next}
            | Some <> as "res" =>
                "consumer" <-{consumer_queue} ‘Some( "queue" ) ;;
                "res"
            end
        end
    end.

Definition bag_2_pop_1 : val :=
  fun: "t" "consumer" =>
    bag_2_pop_0 "consumer" "t".{producers}.

Definition bag_2_pop : val :=
  fun: "t" "consumer" =>
    match: "consumer".{consumer_queue} with
    | None =>
        bag_2_pop_1 "t" "consumer"
    | Some "queue" =>
        match: spmc_queue_pop "queue" with
        | None =>
            bag_2_pop_1 "t" "consumer"
        | Some <> as "res" =>
            "res"
        end
    end.
