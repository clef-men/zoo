Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_parabs.vertex.
Require Import zoo_std.ivar_4.
Require Import examples.vertex_simple__types.
Require Import zoo.options.

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
