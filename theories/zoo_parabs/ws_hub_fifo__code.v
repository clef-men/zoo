From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  domain.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Import
  waiters.
From zoo_parabs Require Import
  ws_hub_fifo__types.
From zoo Require Import
  options.

Definition ws_hub_fifo_create : val :=
  fun: "sz" =>
    { "sz", mpmc_queue_1_create (), waiters_create (), false }.

Definition ws_hub_fifo_size : val :=
  fun: "t" =>
    "t".{size}.

Definition ws_hub_fifo_block : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_hub_fifo_unblock : val :=
  fun: "_t" "_i" =>
    ().

Definition ws_hub_fifo_killed : val :=
  fun: "t" =>
    "t".{killed}.

Definition ws_hub_fifo_notify : val :=
  fun: "t" =>
    waiters_notify "t".{waiters}.

Definition ws_hub_fifo_notify_all : val :=
  fun: "t" =>
    waiters_notify_many "t".{waiters} (ws_hub_fifo_size "t").

Definition ws_hub_fifo_push : val :=
  fun: "t" "_i" "v" =>
    mpmc_queue_1_push "t".{queue} "v" ;;
    ws_hub_fifo_notify "t".

Definition ws_hub_fifo_pop' : val :=
  fun: "t" =>
    mpmc_queue_1_pop "t".{queue}.

Definition ws_hub_fifo_pop : val :=
  fun: "t" "_i" =>
    ws_hub_fifo_pop' "t".

Definition ws_hub_fifo_steal_until_0 : val :=
  rec: "steal_until" "t" "pred" =>
    if: "pred" () then (
      §None
    ) else (
      domain_yield () ;;
      match: ws_hub_fifo_pop' "t" with
      | Some <> as "res" =>
          "res"
      | None =>
          "steal_until" "t" "pred"
      end
    ).

Definition ws_hub_fifo_steal_until : val :=
  fun: "t" "_i" "_max_round_noyield" "pred" =>
    ws_hub_fifo_steal_until_0 "t" "pred".

Definition ws_hub_fifo_steal_0 : val :=
  rec: "steal" "t" =>
    let: "waiters" := "t".{waiters} in
    let: "waiter" := waiters_prepare_wait "waiters" in
    if: ws_hub_fifo_killed "t" then (
      waiters_cancel_wait "waiters" "waiter" ;;
      §None
    ) else (
      if: mpmc_queue_1_is_empty "t".{queue} then (
        waiters_commit_wait "waiters" "waiter"
      ) else (
        waiters_cancel_wait "waiters" "waiter"
      ) ;;
      match: ws_hub_fifo_pop' "t" with
      | Some <> as "res" =>
          "res"
      | None =>
          "steal" "t"
      end
    ).

Definition ws_hub_fifo_steal : val :=
  fun: "t" "_i" "_max_round_noyield" "_max_round_yield" =>
    ws_hub_fifo_steal_0 "t".

Definition ws_hub_fifo_kill : val :=
  fun: "t" =>
    "t" <-{killed} true ;;
    ws_hub_fifo_notify_all "t".

Definition ws_hub_fifo_pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "pred" =>
    match: ws_hub_fifo_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_fifo_steal_until "t" "i" "max_round_noyield" "pred"
    end.

Definition ws_hub_fifo_pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_fifo_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_fifo_steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
