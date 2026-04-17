From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  pool.
From zoo_std Require Import
  ivar_4.
From zoo_parabs Require Import
  future__types.
From zoo Require Import
  options.

Definition future_return : val :=
  ivar_4_make.

Definition future_set : val :=
  fun: "ctx" "t" "res" =>
    ivar_4_notify "t" "ctx" "res".

Definition future_async : val :=
  fun: "ctx" "task" =>
    let: "t" := ivar_4_create () in
    pool_async "ctx" (fun: "ctx" => future_set "ctx" "t" ("task" "ctx")) ;;
    "t".

Definition future_wait : val :=
  fun: "ctx" "t" =>
    pool_wait_ivar "ctx" "t" ;;
    ivar_4_get "t".

Definition future_iter : val :=
  fun: "ctx" "t" "task" =>
    match: ivar_4_wait "t" "task" with
    | None =>
        ()
    | Some "res" =>
        "task" "ctx" "res"
    end.

Definition future_map : val :=
  fun: "ctx" "t1" "task" =>
    let: "t2" := ivar_4_create () in
    future_iter
      "ctx"
      "t1"
      (fun: "ctx" "res1" =>
         pool_async "ctx"
           (fun: "ctx" => future_set "ctx" "t2" ("task" "ctx" "res1"))) ;;
    "t2".
