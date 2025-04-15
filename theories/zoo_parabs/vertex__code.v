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

#[local] Definition __zoo_recs_0 := (
  recs: "release" "ctx" "t" =>
    if: FAA "t".[preds] #(-1) == #1 then (
      pool_silent_async "ctx" (fun: "ctx" => "run" "ctx" "t")
    )
  and: "run" "ctx" "t" =>
    "t".{task} "ctx" ;;
    let: "succs" := mpmc_stack_2_close "t".{succs} in
    clst_iter (fun: "succ" => "release" "ctx" "succ") "succs"
)%zoo_recs.
Definition vertex_release :=
  ValRecs 0 __zoo_recs_0.
Definition vertex_run :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' vertex_release 0 __zoo_recs_0 [
    vertex_release ;
    vertex_run
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' vertex_run 1 __zoo_recs_0 [
    vertex_release ;
    vertex_run
  ].
Proof.
  done.
Qed.
