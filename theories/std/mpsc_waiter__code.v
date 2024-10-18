From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  mutex
  condition.
From zoo.std Require Import
  mpsc_waiter__types.
From zoo Require Import
  options.

Definition mpsc_waiter_create : val :=
  fun: <> =>
    { #false, mutex_create (), condition_create () }.

Definition mpsc_waiter_notify : val :=
  fun: "t" =>
    if: "t".{flag} then (
      #true
    ) else (
      let: "res" :=
        mutex_protect
          "t".{mutex}
          (fun: <> =>
             if: "t".{flag} then (
               #true
             ) else (
               "t" <-{flag} #true ;;
               #false
             ))
      in
      condition_notify "t".{condition} ;;
      "res"
    ).

Definition mpsc_waiter_try_wait : val :=
  fun: "t" =>
    "t".{flag}.

Definition mpsc_waiter_wait : val :=
  fun: "t" =>
    ifnot: mpsc_waiter_try_wait "t" then (
      let: "mtx" := "t".{mutex} in
      let: "cond" := "t".{condition} in
      mutex_protect
        "mtx"
        (fun: <> => condition_wait_until "cond" "mtx" (fun: <> => "t".{flag}))
    ).
