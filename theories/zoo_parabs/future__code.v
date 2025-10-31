From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst
  ivar_3.
From zoo_parabs Require Import
  pool.
From zoo_parabs Require Import
  future__types.
From zoo Require Import
  options.

Definition future_async : val :=
  fun: "ctx" "task" =>
    let: "t" := ivar_3_create () in
    pool_async
      "ctx"
      (fun: "ctx" =>
         let: "res" := "task" "ctx" in
         let: "waiters" := ivar_3_set "t" "res" in
         lst_iter (fun: "waiter" => "waiter" "ctx" "res") "waiters") ;;
    "t".

Definition future_wait : val :=
  fun: "ctx" "t" =>
    pool_wait_until "ctx" (fun: <> => ivar_3_is_set "t") ;;
    ivar_3_get "t".

Definition future_iter : val :=
  fun: "ctx" "t" "fn" =>
    match: ivar_3_wait "t" "fn" with
    | None =>
        ()
    | Some "res" =>
        "fn" "ctx" "res"
    end.

Definition future_map : val :=
  fun: "ctx" "t1" "fn" =>
    let: "t2" := ivar_3_create () in
    future_iter
      "ctx"
      "t1"
      (fun: "ctx" "res1" =>
         let: "res2" := "fn" "ctx" "res1" in
         let: "waiters" := ivar_3_set "t2" "res2" in
         lst_iter (fun: "waiter" => "waiter" "ctx" "res2") "waiters") ;;
    "t2".
