From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt.
From zebre.saturn Require Import
  spsc_latch1
  mpmc_queue.
From zebre.scheduling Require Export
  base.
From zebre.scheduling Require Import
  ws_deques.
From zebre Require Import
  options.

#[local] Notation "'num_round'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'deques'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'foreign'" := (
  in_type "t" 2
)(in custom zebre_field
).
#[local] Notation "'waiters'" := (
  in_type "t" 3
)(in custom zebre_field
).

Section ws_deques.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_deques : ws_deques Σ).

  Definition ws_hub_create : val :=
    λ: "sz" "num_round",
      { "num_round";
        ws_deques.(ws_deques_create) "sz";
        mpmc_queue_create ();
        mpmc_queue_create ()
      }.

  #[local] Definition ws_hub_check_waiters : val :=
    λ: "t",
      match: mpmc_queue_pop "t".{waiters} with
      | None =>
          ()
      | Some "waiter" =>
          spsc_latch1_signal "waiter"
      end.

  Definition ws_hub_push : val :=
    λ: "t" "i" "v",
      ws_deques.(ws_deques_push) "t".{deques} "i" "v" ;;
      ws_hub_check_waiters "t".

  Definition ws_hub_push_foreign : val :=
    λ: "t" "v",
      mpmc_queue_push "t".{foreign} "v" ;;
      ws_hub_check_waiters "t".

  Definition ws_hub_try_pop : val :=
    λ: "t" "i",
      let: "deques" := "t".{deques} in
      match: ws_deques.(ws_deques_pop) "deques" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          match: mpmc_queue_pop "t".{foreign} with
          | Some <> as "res" =>
              "res"
          | None =>
              ws_deques_try_steal_as ws_deques "deques" "i" #1
          end
      end.

  #[local] Definition ws_hub_pop_aux : val :=
    rec: "ws_hub_pop_aux" "t" "i" "n" :=
      if: "n" ≤ #0 then (
        §None
      ) else (
        match: ws_hub_try_pop "t" "i" with
        | Some <> as "res" =>
            "res"
        | None =>
            "ws_hub_pop_aux" "t" "i" ("n" - #1)
        end
      ).
  Definition ws_hub_pop : val :=
    rec: "ws_hub_pop" "t" "i" :=
      match: ws_hub_pop_aux "t" "i" "t".{num_round} with
      | Some "v" =>
          "v"
      | None =>
          let: "waiter" := spsc_latch1_create () in
          mpmc_queue_push "t".{waiters} "waiter" ;;
          spsc_latch1_wait "waiter" ;;
          "ws_hub_pop" "t" "i"
      end.
End ws_deques.

#[global] Opaque ws_hub_create.
#[global] Opaque ws_hub_push.
#[global] Opaque ws_hub_push_foreign.
#[global] Opaque ws_hub_try_pop.
#[global] Opaque ws_hub_pop.
