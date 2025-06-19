From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  lst
  ivar_3
  array
  domain.
From zoo_parabs Require Import
  ws_hub_std.
From zoo_parabs Require Import
  pool__types.
From zoo Require Import
  options.

Definition pool_max_round_noyield : val :=
  #1024.

Definition pool_max_round_yield : val :=
  #32.

Definition pool_context : val :=
  fun: "sz" "hub" "id" =>
    ("sz", "hub", "id").

Definition pool_execute : val :=
  fun: "ctx" "job" =>
    "job" "ctx".

Definition pool_worker : val :=
  rec: "worker" "ctx" =>
    match:
      ws_hub_std_pop_steal
        "ctx".<context_hub>
        "ctx".<context_id>
        pool_max_round_noyield
        pool_max_round_yield
    with
    | None =>
        ws_hub_std_block "ctx".<context_hub> "ctx".<context_id>
    | Some "job" =>
        pool_execute "ctx" "job" ;;
        "worker" "ctx"
    end.

Definition pool_create : val :=
  fun: "sz" =>
    let: "hub" := ws_hub_std_create ("sz" + #1) in
    ws_hub_std_block "hub" #0 ;;
    let: "domains" :=
      array_unsafe_initi
        "sz"
        (fun: "i" =>
           domain_spawn
             (fun: <> => pool_worker (pool_context "sz" "hub" ("i" + #1))))
    in
    ("sz", "hub", "domains").

Definition pool_run : val :=
  fun: "t" "job" =>
    ws_hub_std_unblock "t".<hub> #0 ;;
    let: "res" :=
      pool_execute (pool_context "t".<size> "t".<hub> #0) "job"
    in
    ws_hub_std_block "t".<hub> #0 ;;
    "res".

Definition pool_kill : val :=
  fun: "t" =>
    ws_hub_std_kill "t".<hub> ;;
    array_iter domain_join "t".<domains>.

Definition pool_size : val :=
  fun: "ctx" =>
    "ctx".<context_size>.

Definition pool_async_silent : val :=
  fun: "ctx" "task" =>
    ws_hub_std_push "ctx".<context_hub> "ctx".<context_id> "task".

Definition pool_async : val :=
  fun: "ctx" "task" =>
    let: "fut" := ivar_3_create () in
    pool_async_silent
      "ctx"
      (fun: "ctx" =>
         let: "res" := "task" "ctx" in
         let: "waiters" := ivar_3_set "fut" "res" in
         lst_iter (fun: "waiter" => "waiter" "ctx" "res") "waiters") ;;
    "fut".

Definition pool_wait_until : val :=
  rec: "wait_until" "ctx" "pred" =>
    if: ~ "pred" () then (
      match:
        ws_hub_std_pop_steal_until
          "ctx".<context_hub>
          "ctx".<context_id>
          pool_max_round_noyield
          "pred"
      with
      | None =>
          ()
      | Some "job" =>
          pool_execute "ctx" "job" ;;
          "wait_until" "ctx" "pred"
      end
    ).

Definition pool_wait_while : val :=
  fun: "ctx" "pred" =>
    pool_wait_until "ctx" (fun: <> => ~ "pred" ()).

Definition pool_wait : val :=
  fun: "ctx" "fut" =>
    pool_wait_until "ctx" (fun: <> => ivar_3_is_set "fut") ;;
    ivar_3_get "fut".

Definition pool_iter : val :=
  fun: "ctx" "fut" "fn" =>
    match: ivar_3_wait "fut" "fn" with
    | None =>
        ()
    | Some "res" =>
        "fn" "ctx" "res"
    end.

Definition pool_map : val :=
  fun: "ctx" "fut1" "fn" =>
    let: "fut2" := ivar_3_create () in
    pool_iter
      "ctx"
      "fut1"
      (fun: "ctx" "res1" =>
         let: "res2" := "fn" "ctx" "res1" in
         let: "waiters" := ivar_3_set "fut2" "res2" in
         lst_iter (fun: "waiter" => "waiter" "ctx" "res2") "waiters") ;;
    "fut2".
