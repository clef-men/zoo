From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo_std Require Import
  semaphore__types.
From zoo Require Import
  options.

Definition semaphore٠create : val :=
  fun: "cap" =>
    { mutex٠create (), condition٠create (), "cap" - 1 }.

Definition semaphore٠try_lock : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         let: "cnt" := "t".{count} in
         if: 0 < "cnt" then (
           "t" <-{count} "cnt" - 1 ;;
           true
         ) else (
           false
         )).

Definition semaphore٠lock : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex}
      (fun: <> =>
         condition٠wait_until
           "t".{condition}
           "t".{mutex}
           (fun: <> => 0 < "t".{count}) ;;
         "t" <-{count} "t".{count} - 1).

Definition semaphore٠unlock : val :=
  fun: "t" =>
    mutex٠protect "t".{mutex} (fun: <> => "t" <-{count} "t".{count} + 1) ;;
    condition٠notify "t".{condition}.
