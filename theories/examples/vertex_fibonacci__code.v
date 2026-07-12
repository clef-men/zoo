Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_parabs.vertex.
Require Import zoo_std.ivar_4.
Require Import examples.vertex_fibonacci__types.
Require Import zoo.options.

Definition vertex_fibonacci٠main₀ : val :=
  rec: "main" "ctx" "vtx" "r" "n" =>
    if: "n" ≤ 1 then (
      "r" <- "n" ;;
      true
    ) else (
      let: "r1" := ref 0 in
      let: "vtx1" := vertex٠create §None in
      let: "n1" := "n" - 1 in
      vertex٠set_task "vtx1" (fun: "ctx" => "main" "ctx" "vtx1" "r1" "n1") ;;
      vertex٠release "ctx" "vtx1" ;;
      let: "r2" := ref 0 in
      let: "vtx2" := vertex٠create §None in
      let: "n2" := "n" - 2 in
      vertex٠set_task "vtx2" (fun: "ctx" => "main" "ctx" "vtx2" "r2" "n2") ;;
      vertex٠release "ctx" "vtx2" ;;
      vertex٠precede "vtx1" "vtx" ;;
      vertex٠precede "vtx2" "vtx" ;;
      vertex٠yield "vtx" (fun: "_ctx" => "r" <- !"r1" + !"r2" ;;
                                          true)
    ).

Definition vertex_fibonacci٠main : val :=
  fun: "num_worker" "n" =>
    pool٠run
      "num_worker"
      (fun: "ctx" =>
         let: "r" := ref 0 in
         let: "vtx1" := vertex٠create §None in
         vertex٠set_task
           "vtx1"
           (fun: "ctx" => vertex_fibonacci٠main₀ "ctx" "vtx1" "r" "n") ;;
         vertex٠release "ctx" "vtx1" ;;
         let: "ivar" := ivar_4٠create () in
         let: "vtx2" :=
           vertex٠create' (fun: "ctx" => ivar_4٠notify "ivar" "ctx" ())
         in
         vertex٠precede "vtx1" "vtx2" ;;
         vertex٠release "ctx" "vtx2" ;;
         pool٠wait_ivar "ctx" "ivar" ;;
         !"r").
