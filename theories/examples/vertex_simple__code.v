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

Definition vertex_simple٠main : val :=
  fun: "num_worker" "a" "b" "c" "d" =>
    let: "ivar" := ivar_4٠create () in
    let: "vtx_a" := vertex٠create' (fun: "_ctx" => "a" ()) in
    let: "vtx_b" := vertex٠create' (fun: "_ctx" => "b" ()) in
    let: "vtx_c" := vertex٠create' (fun: "_ctx" => "c" ()) in
    let: "vtx_d" :=
      vertex٠create' (fun: "ctx" => "d" () ;;
                                     ivar_4٠notify "ivar" "ctx" ())
    in
    vertex٠precede "vtx_a" "vtx_b" ;;
    vertex٠precede "vtx_a" "vtx_c" ;;
    vertex٠precede "vtx_b" "vtx_d" ;;
    vertex٠precede "vtx_c" "vtx_d" ;;
    pool٠run
      "num_worker"
      (fun: "ctx" =>
         vertex٠release "ctx" "vtx_d" ;;
         vertex٠release "ctx" "vtx_c" ;;
         vertex٠release "ctx" "vtx_b" ;;
         vertex٠release "ctx" "vtx_a" ;;
         pool٠wait_ivar "ctx" "ivar").
