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

Definition waiters_create : val :=
  fun: "sz" =>
    (array_unsafe_init "sz" waiter_create, mpmc_queue_1_create ()).

Definition waiters_notify : val :=
  fun: "t" "i" =>
    let: "waiter" := array_unsafe_get "t".<waiters> "i" in
    waiter_notify_strong "waiter".

Definition waiters_notify_one : val :=
  rec: "notify_one" "t" =>
    match: mpmc_queue_1_pop "t".<queue> with
    | None =>
        ()
    | Some "waiter" =>
        if: ~ waiter_notify "waiter" then (
          "notify_one" "t"
        )
    end.

Definition waiters_notify_all : val :=
  rec: "notify_all" "t" =>
    match: mpmc_queue_1_pop "t".<queue> with
    | None =>
        ()
    | Some "waiter" =>
        waiter_notify "waiter" ;;
        "notify_all" "t"
    end.

Definition waiters_prepare_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array_unsafe_get "t".<waiters> "i" in
    waiter_prepare_wait "waiter" ;;
    mpmc_queue_1_push "t".<queue> "waiter".

Definition waiters_cancel_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array_unsafe_get "t".<waiters> "i" in
    waiter_cancel_wait "waiter".

Definition waiters_commit_wait : val :=
  fun: "t" "i" =>
    let: "waiter" := array_unsafe_get "t".<waiters> "i" in
    waiter_commit_wait "waiter".
