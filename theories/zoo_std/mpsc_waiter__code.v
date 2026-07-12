Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_std.mpsc_waiter__types.
Require Import zoo.options.

Definition mpsc_waiter٠create : val :=
  fun: <> =>
    { mutex٠create (), condition٠create (), false }.

Definition mpsc_waiter٠notify : val :=
  fun: "t" =>
    if: "t".{flag} then (
      true
    ) else (
      let: "res" :=
        mutex٠protect "t".{mutex}
          (fun: <> =>
             if: "t".{flag} then (
               true
             ) else (
               "t" <-{flag} true ;;
               false
             ))
      in
      condition٠notify "t".{condition} ;;
      "res"
    ).

Definition mpsc_waiter٠try_wait : val :=
  fun: "t" =>
    "t".{flag}.

Definition mpsc_waiter٠wait : val :=
  fun: "t" =>
    if: ~ mpsc_waiter٠try_wait "t" then (
      let: "mtx" := "t".{mutex} in
      let: "cond" := "t".{condition} in
      mutex٠protect "mtx"
        (fun: <> =>
           condition٠wait_until "cond" "mtx" (fun: <> => "t".{flag}))
    ).
