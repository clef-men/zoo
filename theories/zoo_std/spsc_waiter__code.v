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

Definition spsc_waiter٠create : val :=
  fun: <> =>
    { mutex٠create (), condition٠create (), false }.

Definition spsc_waiter٠notify : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex} (fun: <> => "t" <-{flag} true) ;;
    condition٠notify "t".{condition}.

Definition spsc_waiter٠try_wait : val :=
  fun: "t" =>
    "t".{flag}.

Definition spsc_waiter٠wait : val :=
  fun: "t" =>
    if: ~ spsc_waiter٠try_wait "t" then (
      let: "mtx" := "t".{mutex} in
      let: "cond" := "t".{condition} in
      mutex٠protect "mtx"
        (fun: <> =>
           condition٠wait_until "cond" "mtx" (fun: <> => "t".{flag}))
    ).
