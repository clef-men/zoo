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

Definition future٠return : val :=
  ivar_4٠make.

Definition future٠set : val :=
  fun: "ctx" "t" "res" =>
    ivar_4٠notify "t" "ctx" "res".

Definition future٠async : val :=
  fun: "ctx" "task" =>
    let: "t" := ivar_4٠create () in
    pool٠async "ctx" (fun: "ctx" => future٠set "ctx" "t" ("task" "ctx")) ;;
    "t".

Definition future٠wait : val :=
  fun: "ctx" "t" =>
    pool٠wait_ivar "ctx" "t" ;;
    ivar_4٠get "t".

Definition future٠iter : val :=
  fun: "ctx" "t" "task" =>
    match: ivar_4٠wait "t" "task" with
    | None =>
        ()
    | Some "res" =>
        "task" "ctx" "res"
    end.

Definition future٠map : val :=
  fun: "ctx" "t1" "task" =>
    let: "t2" := ivar_4٠create () in
    future٠iter
      "ctx"
      "t1"
      (fun: "ctx" "res1" =>
         pool٠async "ctx"
           (fun: "ctx" => future٠set "ctx" "t2" ("task" "ctx" "res1"))) ;;
    "t2".
