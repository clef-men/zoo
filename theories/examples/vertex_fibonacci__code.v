From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  pool
  vertex.
From zoo_std Require Import
  ivar_3.
From examples Require Import
  vertex_fibonacci__types.
From zoo Require Import
  options.

Definition vertex_fibonacci_main₀ : val :=
  rec: "main" "ctx" "vtx" "r" "n" =>
    if: "n" ≤ 1 then (
      "r" <- "n" ;;
      true
    ) else (
      let: "r1" := ref 0 in
      let: "vtx1" := vertex_create §None in
      let: "n1" := "n" - 1 in
      vertex_set_task "vtx1" (fun: "ctx" => "main" "ctx" "vtx1" "r1" "n1") ;;
      vertex_release "ctx" "vtx1" ;;
      let: "r2" := ref 0 in
      let: "vtx2" := vertex_create §None in
      let: "n2" := "n" - 2 in
      vertex_set_task "vtx2" (fun: "ctx" => "main" "ctx" "vtx2" "r2" "n2") ;;
      vertex_release "ctx" "vtx2" ;;
      vertex_precede "vtx1" "vtx" ;;
      vertex_precede "vtx2" "vtx" ;;
      vertex_yield "vtx" (fun: "_ctx" => "r" <- !"r1" + !"r2" ;;
                                         true)
    ).

Definition vertex_fibonacci_main : val :=
  fun: "num_worker" "n" =>
    pool_run
      "num_worker"
      (fun: "ctx" =>
         let: "r" := ref 0 in
         let: "vtx1" := vertex_create §None in
         vertex_set_task
           "vtx1"
           (fun: "ctx" => vertex_fibonacci_main₀ "ctx" "vtx1" "r" "n") ;;
         vertex_release "ctx" "vtx1" ;;
         let: "ivar" := ivar_3_create () in
         let: "vtx2" :=
           vertex_create' (fun: "ctx" => ivar_3_notify "ivar" "ctx")
         in
         vertex_precede "vtx1" "vtx2" ;;
         vertex_release "ctx" "vtx2" ;;
         pool_wait_ivar "ctx" "ivar" ;;
         !"r").
