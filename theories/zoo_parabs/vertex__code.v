Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_saturn.mpmc_stack_2.
Require Import zoo_std.clist.
Require Import zoo_parabs.vertex__types.
Require Import zoo.options.

Definition vertex٠create : val :=
  fun: "task" =>
    let: "task" :=
      match: "task" with
      | Some "task" =>
          "task"
      | None =>
          fun: <> => true
      end
    in
    { "task", 1, mpmc_stack_2٠create () }.

Definition vertex٠create' : val :=
  fun: "task" =>
    vertex٠create ‘Some( fun: "ctx" => "task" "ctx" ;;
                                          true ).

Definition vertex٠task : val :=
  fun: "t" =>
    "t".{task}.

Definition vertex٠set_task : val :=
  fun: "t" "task" =>
    "t" <-{task} "task".

Definition vertex٠precede : val :=
  fun: "t1" "t2" =>
    let: "succs1" := "t1".{succs} in
    if: ~ mpmc_stack_2٠is_closed "succs1" then (
      FAA "t2".[preds] 1 ;;
      if: mpmc_stack_2٠push "succs1" "t2" then (
        FAA "t2".[preds] (-1) ;;
        ()
      )
    ).

#[local] Definition __zoo_recs_0 :=
  ( recs: "release" "ctx" "t" =>
      if: FAA "t".[preds] (-1) == 1 then (
        "run" "ctx" "t"
      )
    and: "run" "ctx" "t" =>
      pool٠async "ctx"
        (fun: "ctx" =>
           "t" <-{preds} 1 ;;
           if: "t".{task} "ctx" then (
             let: "succs" := mpmc_stack_2٠close "t".{succs} in
             clist٠iter (fun: "succ" => "release" "ctx" "succ") "succs"
           ) else (
             "release" "ctx" "t"
           ))
  )%zoo_recs.
Definition vertex٠release :=
  ValRecs 0 __zoo_recs_0.
Definition vertex٠run :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' vertex٠release 0 __zoo_recs_0 [
    vertex٠release ;
    vertex٠run
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' vertex٠run 1 __zoo_recs_0 [
    vertex٠release ;
    vertex٠run
  ].
Proof.
  done.
Qed.

Definition vertex٠yield : val :=
  fun: "vtx" "task" =>
    vertex٠set_task "vtx" "task" ;;
    false.
