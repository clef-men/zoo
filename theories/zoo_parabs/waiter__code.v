From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo_parabs Require Import
  waiter__types.
From zoo Require Import
  options.

Definition waiter_create : val :=
  fun: <> =>
    { mutex_create (), condition_create (), false }.

Definition waiter_notify : val :=
  fun: "t" =>
    if: "t".{flag} then (
      false
    ) else (
      mutex_lock "t".{mutex} ;;
      if: "t".{flag} then (
        mutex_unlock "t".{mutex} ;;
        false
      ) else (
        "t" <-{flag} true ;;
        mutex_unlock "t".{mutex} ;;
        condition_notify "t".{condition} ;;
        true
      )
    ).

Definition waiter_prepare_wait : val :=
  fun: "t" =>
    "t" <-{flag} false.

Definition waiter_cancel_wait : val :=
  fun: "t" =>
    "t" <-{flag} true.

Definition waiter_commit_wait : val :=
  fun: "t" =>
    if: ~ "t".{flag} then (
      mutex_protect "t".{mutex}
        (fun: <> =>
           condition_wait_until
             "t".{condition}
             "t".{mutex}
             (fun: <> => "t".{flag}))
    ).
