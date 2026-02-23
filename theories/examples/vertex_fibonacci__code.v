From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  mpsc_flag.
From zoo_parabs Require Import
  pool
  vertex.
From examples Require Import
  vertex_fibonacci__types.
From zoo Require Import
  options.

Definition vertex_fibonacci_main_0 : val :=
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
  fun: "num_dom" "n" =>
    let: "pool" := pool_create "num_dom" in
    let: "res" :=
      pool_run "pool"
        (fun: "ctx" =>
           let: "r" := ref 0 in
           let: "vtx1" := vertex_create §None in
           vertex_set_task
             "vtx1"
             (fun: "ctx" => vertex_fibonacci_main_0 "ctx" "vtx1" "r" "n") ;;
           vertex_release "ctx" "vtx1" ;;
           let: "flag" := mpsc_flag_create () in
           let: "vtx2" :=
             vertex_create' (fun: "_ctx" => mpsc_flag_set "flag")
           in
           vertex_precede "vtx1" "vtx2" ;;
           vertex_release "ctx" "vtx2" ;;
           pool_wait_until "ctx" (fun: <> => mpsc_flag_get "flag") ;;
           !"r")
    in
    pool_kill "pool" ;;
    "res".
