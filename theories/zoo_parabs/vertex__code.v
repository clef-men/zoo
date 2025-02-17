From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  clst.
From zoo_saturn Require Import
  mpmc_stack_2.
From zoo_parabs Require Import
  pool.
From zoo_parabs Require Import
  vertex__types.
From zoo Require Import
  options.

Definition vertex_create : val :=
  fun: "task" =>
    { "task", #1, mpmc_stack_2_create () }.

Definition vertex_precede : val :=
  fun: "t1" "t2" =>
    let: "succs1" := "t1".{succs} in
    if: ~ mpmc_stack_2_is_closed "succs1" then (
      FAA "t2".[preds] #1 ;;
      if: mpmc_stack_2_push "succs1" "t2" then (
        FAA "t2".[preds] #(-1) ;;
        ()
      )
    ).

Definition vertex_propagate : val :=
  fun: "ctx" "t" "run" =>
    if: FAA "t".[preds] #(-1) == #1 then (
      pool_silent_async "ctx" (fun: "ctx" => "run" "ctx" "t")
    ).

Definition vertex_run : val :=
  rec: "run" "ctx" "t" =>
    "t".{task} "ctx" ;;
    let: "succs" := mpmc_stack_2_close "t".{succs} in
    clst_iter (fun: "t'" => vertex_propagate "ctx" "t'" "run") "succs".

Definition vertex_release : val :=
  fun: "ctx" "t" =>
    vertex_propagate "ctx" "t" vertex_run.
