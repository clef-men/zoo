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

Definition semaphore_create : val :=
  fun: "cap" =>
    { mutex_create (), condition_create (), "cap" - #1 }.

Definition semaphore_try_lock : val :=
  fun: "t" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         let: "cnt" := "t".{count} in
         if: #0 < "cnt" then (
           "t" <-{count} "cnt" - #1 ;;
           #true
         ) else (
           #false
         )).

Definition semaphore_lock : val :=
  fun: "t" =>
    mutex_protect "t".{mutex}
      (fun: <> =>
         condition_wait_until
           "t".{condition}
           "t".{mutex}
           (fun: <> => #0 < "t".{count}) ;;
         "t" <-{count} "t".{count} - #1).

Definition semaphore_unlock : val :=
  fun: "t" =>
    mutex_protect "t".{mutex} (fun: <> => "t" <-{count} "t".{count} + #1) ;;
    condition_notify "t".{condition}.
