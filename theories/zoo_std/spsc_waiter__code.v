From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo_std Require Import
  spsc_waiter__types.
From zoo Require Import
  options.

Definition spsc_waiter_create : val :=
  fun: <> =>
    { #false, mutex_create (), condition_create () }.

Definition spsc_waiter_notify : val :=
  fun: "t" =>
    mutex_protect "t".{mutex} (fun: <> => "t" <-{flag} #true) ;;
    condition_notify "t".{condition}.

Definition spsc_waiter_try_wait : val :=
  fun: "t" =>
    "t".{flag}.

Definition spsc_waiter_wait : val :=
  fun: "t" =>
    if: ~ spsc_waiter_try_wait "t" then (
      let: "mtx" := "t".{mutex} in
      let: "cond" := "t".{condition} in
      mutex_protect "mtx"
        (fun: <> => condition_wait_until "cond" "mtx" (fun: <> => "t".{flag}))
    ).
