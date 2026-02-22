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
  vertex_simple__types.
From zoo Require Import
  options.

Definition vertex_simple_main : val :=
  fun: "num_dom" "a" "b" "c" "d" =>
    let: "flag" := mpsc_flag_create () in
    let: "vtx_a" := vertex_create ‘Some( fun: "_ctx" => "a" () ) in
    let: "vtx_b" := vertex_create ‘Some( fun: "_ctx" => "b" () ) in
    let: "vtx_c" := vertex_create ‘Some( fun: "_ctx" => "c" () ) in
    let: "vtx_d" :=
      vertex_create ‘Some( fun: "_ctx" => "d" () ;;
                                            mpsc_flag_set "flag" )
    in
    vertex_precede "vtx_a" "vtx_b" ;;
    vertex_precede "vtx_a" "vtx_c" ;;
    vertex_precede "vtx_b" "vtx_d" ;;
    vertex_precede "vtx_c" "vtx_d" ;;
    let: "pool" := pool_create "num_dom" in
    pool_run
      "pool"
      (fun: "ctx" =>
         vertex_release "ctx" "vtx_d" ;;
         vertex_release "ctx" "vtx_c" ;;
         vertex_release "ctx" "vtx_b" ;;
         vertex_release "ctx" "vtx_a" ;;
         pool_wait_until "ctx" (fun: <> => mpsc_flag_get "flag")) ;;
    pool_kill "pool".
