From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mpsc_waiter.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Import
  waiters__types.
From zoo Require Import
  options.

Definition waiters_create : val :=
  mpmc_queue_1_create.

Definition waiters_notify' : val :=
  rec: "notify'" "t" =>
    match: mpmc_queue_1_pop "t" with
    | None =>
        #false
    | Some "waiter" =>
        if: mpsc_waiter_notify "waiter" then (
          "notify'" "t"
        ) else (
          #true
        )
    end.

Definition waiters_notify : val :=
  fun: "t" =>
    waiters_notify' "t" ;;
    ().

Definition waiters_notify_many : val :=
  rec: "notify_many" "t" "n" =>
    if: #0 < "n" and waiters_notify' "t" then (
      "notify_many" "t" ("n" - #1)
    ).

Definition waiters_prepare_wait : val :=
  fun: "t" =>
    let: "waiter" := mpsc_waiter_create () in
    mpmc_queue_1_push "t" "waiter" ;;
    "waiter".

Definition waiters_cancel_wait : val :=
  fun: "t" "waiter" =>
    if: mpsc_waiter_notify "waiter" then (
      waiters_notify "t"
    ).

Definition waiters_commit_wait : val :=
  fun: "_t" "waiter" =>
    mpsc_waiter_wait "waiter".
