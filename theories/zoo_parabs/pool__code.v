From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  ws_hub_std.
From zoo_std Require Import
  ivar_4
  array
  domain.
From zoo_parabs Require Import
  pool__types.
From zoo Require Import
  options.

Definition pool_max_round_noyield : val :=
  1024.

Definition pool_max_round_yield : val :=
  32.

Definition pool_context : val :=
  fun: "sz" "hub" "id" =>
    ("sz", "hub", "id").

Definition pool_context_main : val :=
  fun: "t" =>
    pool_context "t".{size} "t".{hub} 0.

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
        ()
    | Some "job" =>
        pool_execute "ctx" "job" ;;
        "worker" "ctx"
    end.

Definition pool_create : val :=
  fun: "sz" =>
    let: "hub" := ws_hub_std_create ("sz" + 1) in
    ws_hub_std_block "hub" 0 ;;
    let: "domains" :=
      array_unsafe_initi
        "sz"
        (fun: "i" =>
           domain_spawn
             (fun: <> => pool_worker (pool_context "sz" "hub" ("i" + 1))))
    in
    { "sz", "hub", "domains", () }.

Definition pool_run_on : val :=
  fun: "t" "task" =>
    ws_hub_std_unblock "t".{hub} 0 ;;
    let: "res" := pool_execute (pool_context_main "t") "task" in
    ws_hub_std_block "t".{hub} 0 ;;
    "res".

Definition pool_close : val :=
  fun: "t" =>
    ws_hub_std_close "t".{hub} ;;
    ws_hub_std_unblock "t".{hub} 0 ;;
    pool_worker (pool_context_main "t") ;;
    array_iter domain_join "t".{domains}.

Definition pool_run : val :=
  fun: "num_worker" "task" =>
    let: "t" := pool_create "num_worker" in
    let: "res" := pool_run_on "t" "task" in
    pool_close "t" ;;
    "res".

Definition pool_size : val :=
  fun: "ctx" =>
    "ctx".<context_size>.

Definition pool_async : val :=
  fun: "ctx" "task" =>
    ws_hub_std_push "ctx".<context_hub> "ctx".<context_id> "task".

Definition pool_wait₀ : val :=
  rec: "wait" "ctx" "notification" "pred" =>
    match:
      ws_hub_std_pop_steal_until
        "ctx".<context_hub>
        "ctx".<context_id>
        pool_max_round_noyield
        pool_max_round_yield
        "notification"
        "pred"
    with
    | None =>
        ()
    | Some "job" =>
        pool_execute "ctx" "job" ;;
        "wait" "ctx" "notification" "pred"
    end.

Definition pool_wait : val :=
  fun: "ctx" "notification" "pred" =>
    let: "notification_registered" := ref false in
    let: "notification" "notify" :=
      if: ~ !"notification_registered" then (
        "notification_registered" <- true ;;
        "notification" "notify"
      )
    in
    pool_wait₀ "ctx" "notification" "pred".

Definition pool_wait_ivar : val :=
  fun: "ctx" "ivar" =>
    pool_wait
      "ctx"
      (fun: "notify" =>
         ivar_4_wait "ivar" (fun: "_ctx" "_v" => "notify" ()) ;;
         ())
      (fun: <> => ivar_4_is_set "ivar").
