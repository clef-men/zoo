From zebre Require Import
  prelude.
From zebre.language Require Import
  notations.
From zebre.std Require Import
  opt.
From zebre.saturn Require Import
  spmc_future.
From zebre.scheduling Require Export
  base.
From zebre.scheduling Require Import
  ws_deques
  ws_hub.
From zebre Require Import
  options.

#[local] Notation "'hub'" := (
  in_type "handle" 0
)(in custom zebre_proj
).
#[local] Notation "'id'" := (
  in_type "handle" 1
)(in custom zebre_proj
).

Section ws_deques.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_deques : ws_deques Σ).

  #[local] Definition scheduler_worker : val :=
    rec: "scheduler_worker" "hdl" :=
      let: "task" := ws_hub_pop ws_deques "hdl".<hub> "hdl".<id> in
      "task" "hdl" ;;
      "scheduler_worker" "hdl".

  Definition scheduler_create : val :=
    λ: "sz",
      let: "t" := ws_hub_create ws_deques (#1 + "sz") in
      for: "i" := #1 to #1 + "sz" begin
        Fork (scheduler_worker ("t", "i"))
      end ;;
      "t".

  Definition scheduler_run : val :=
    λ: "t" "task",
      "task" ("t", #0).

  Definition scheduler_async : val :=
    λ: "hdl" "task",
      let: "fut" := spmc_future_create () in
      ws_hub_push ws_deques "hdl".<hub> "hdl".<id> (λ: "hdl",
        spmc_future_set "fut" ("task" "hdl")
      ) ;;
      "fut".

  Definition scheduler_await : val :=
    rec: "scheduler_await" "hdl" "fut" :=
      match: spmc_future_try_get "fut" with
      | Some "res" =>
          "res"
      | None =>
          let: "task" := ws_hub_pop ws_deques "hdl".<hub> "hdl".<id> in
          "task" "hdl" ;;
          "scheduler_await" "hdl" "fut"
      end.
End ws_deques.

#[global] Opaque scheduler_create.
#[global] Opaque scheduler_run.
#[global] Opaque scheduler_async.
#[global] Opaque scheduler_await.
