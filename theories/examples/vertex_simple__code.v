From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  pool
  vertex.
From zoo_std Require Import
  ivar_4.
From examples Require Import
  vertex_simple__types.
From zoo Require Import
  options.

Definition vertex_simple_main : val :=
  fun: "num_worker" "a" "b" "c" "d" =>
    let: "ivar" := ivar_4_create () in
    let: "vtx_a" := vertex_create' (fun: "_ctx" => "a" ()) in
    let: "vtx_b" := vertex_create' (fun: "_ctx" => "b" ()) in
    let: "vtx_c" := vertex_create' (fun: "_ctx" => "c" ()) in
    let: "vtx_d" :=
      vertex_create' (fun: "ctx" => "d" () ;;
                                    ivar_4_notify "ivar" "ctx" ())
    in
    vertex_precede "vtx_a" "vtx_b" ;;
    vertex_precede "vtx_a" "vtx_c" ;;
    vertex_precede "vtx_b" "vtx_d" ;;
    vertex_precede "vtx_c" "vtx_d" ;;
    pool_run
      "num_worker"
      (fun: "ctx" =>
         vertex_release "ctx" "vtx_d" ;;
         vertex_release "ctx" "vtx_c" ;;
         vertex_release "ctx" "vtx_b" ;;
         vertex_release "ctx" "vtx_a" ;;
         pool_wait_ivar "ctx" "ivar").
