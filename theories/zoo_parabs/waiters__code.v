From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  waiter.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_std Require Import
  array.
From zoo_parabs Require Import
  waiters__types.
From zoo Require Import
  options.

Definition waiters٠create : val :=
  fun: "sz" =>
    (array٠unsafe_init "sz" waiter٠create, mpmc_queue_1٠create ()).

Definition waiters٠notify : val :=
  fun: "t" "i" =>
    let: "waiter" := array٠unsafe_get "t".<waiters> "i" in
    waiter٠notify "waiter" ;;
    ().

Definition waiters٠notify_one : val :=
  rec: "notify_one" "t" =>
    match: mpmc_queue_1٠pop "t".<queue> with
    | None =>
        ()
    | Some "waiter" =>
        if: ~ waiter٠notify "waiter" then (
          "notify_one" "t"
        )
    end.

Definition waiters٠notify_all : val :=
  rec: "notify_all" "t" =>
    match: mpmc_queue_1٠pop "t".<queue> with
    | None =>
        ()
    | Some "waiter" =>
        waiter٠notify "waiter" ;;
        "notify_all" "t"
    end.

Definition waiters٠prepare_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array٠unsafe_get "t".<waiters> "i" in
    waiter٠prepare_wait "waiter" ;;
    mpmc_queue_1٠push "t".<queue> "waiter".

Definition waiters٠cancel_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array٠unsafe_get "t".<waiters> "i" in
    waiter٠cancel_wait "waiter".

Definition waiters٠commit_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array٠unsafe_get "t".<waiters> "i" in
    waiter٠commit_wait "waiter".
