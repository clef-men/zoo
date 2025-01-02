From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_saturn Require Import
  spmc_queue
  mpmc_stack_1.
From zoo_saturn Require Import
  bag_2__types.
From zoo Require Import
  options.

Definition bag_2_create : val :=
  mpmc_stack_1_create.

Definition bag_2_create_producer : val :=
  fun: "t" =>
    let: "producer" := spmc_queue_create () in
    mpmc_stack_1_push "t" "producer" ;;
    "producer".

Definition bag_2_create_consumer : val :=
  fun: "_t" =>
    ref §None.

Definition bag_2_push : val :=
  fun: "producer" "v" =>
    spmc_queue_push "producer" "v".

Definition bag_2_pop_0 : val :=
  rec: "pop" "producers" "consumer" =>
    match: "producers" with
    | [] =>
        §None
    | "producer" :: "producers" =>
        match: spmc_queue_pop "producer" with
        | None =>
            "pop" "producers" "consumer"
        | Some <> as "res" =>
            "consumer" <- ‘Some( "producer" ) ;;
            "res"
        end
    end.

Definition bag_2_pop_1 : val :=
  fun: "t" "consumer" =>
    bag_2_pop_0 (mpmc_stack_1_snapshot "t") "consumer".

Definition bag_2_pop : val :=
  fun: "t" "consumer" =>
    match: !"consumer" with
    | None =>
        bag_2_pop_1 "t" "consumer"
    | Some "producer" =>
        match: spmc_queue_pop "producer" with
        | None =>
            bag_2_pop_1 "t" "consumer"
        | Some <> as "res" =>
            "res"
        end
    end.
