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

Definition pool٠max_round_noyield : val :=
  1024.

Definition pool٠max_round_yield : val :=
  32.

Definition pool٠context : val :=
  fun: "sz" "hub" "id" =>
    ("sz", "hub", "id").

Definition pool٠context_main : val :=
  fun: "t" =>
    pool٠context "t".{size} "t".{hub} 0.

Definition pool٠execute : val :=
  fun: "ctx" "job" =>
    "job" "ctx".

Definition pool٠worker : val :=
  rec: "worker" "ctx" =>
    match:
      ws_hub_std٠pop_steal
        "ctx".<context_hub>
        "ctx".<context_id>
        pool٠max_round_noyield
        pool٠max_round_yield
    with
    | None =>
        ()
    | Some "job" =>
        pool٠execute "ctx" "job" ;;
        "worker" "ctx"
    end.

Definition pool٠create : val :=
  fun: "sz" =>
    let: "hub" := ws_hub_std٠create ("sz" + 1) in
    ws_hub_std٠block "hub" 0 ;;
    let: "domains" :=
      array٠unsafe_initi
        "sz"
        (fun: "i" =>
           domain٠spawn
             (fun: <> => pool٠worker (pool٠context "sz" "hub" ("i" + 1))))
    in
    { "sz", "hub", "domains", () }.

Definition pool٠run_on : val :=
  fun: "t" "task" =>
    ws_hub_std٠unblock "t".{hub} 0 ;;
    let: "res" := pool٠execute (pool٠context_main "t") "task" in
    ws_hub_std٠block "t".{hub} 0 ;;
    "res".

Definition pool٠close : val :=
  fun: "t" =>
    ws_hub_std٠close "t".{hub} ;;
    ws_hub_std٠unblock "t".{hub} 0 ;;
    pool٠worker (pool٠context_main "t") ;;
    array٠iter domain٠join "t".{domains}.

Definition pool٠run : val :=
  fun: "num_worker" "task" =>
    let: "t" := pool٠create "num_worker" in
    let: "res" := pool٠run_on "t" "task" in
    pool٠close "t" ;;
    "res".

Definition pool٠size : val :=
  fun: "ctx" =>
    "ctx".<context_size>.

Definition pool٠async : val :=
  fun: "ctx" "task" =>
    ws_hub_std٠push "ctx".<context_hub> "ctx".<context_id> "task".

Definition pool٠wait₀ : val :=
  rec: "wait" "ctx" "notification" "pred" =>
    match:
      ws_hub_std٠pop_steal_until
        "ctx".<context_hub>
        "ctx".<context_id>
        pool٠max_round_noyield
        pool٠max_round_yield
        "notification"
        "pred"
    with
    | None =>
        ()
    | Some "job" =>
        pool٠execute "ctx" "job" ;;
        "wait" "ctx" "notification" "pred"
    end.

Definition pool٠wait : val :=
  fun: "ctx" "notification" "pred" =>
    let: "notification_registered" := ref false in
    let: "notification" "notify" :=
      if: ~ !"notification_registered" then (
        "notification_registered" <- true ;;
        "notification" "notify"
      )
    in
    pool٠wait₀ "ctx" "notification" "pred".

Definition pool٠wait_ivar : val :=
  fun: "ctx" "ivar" =>
    pool٠wait
      "ctx"
      (fun: "notify" =>
         ivar_4٠wait "ivar" (fun: "_ctx" "_v" => "notify" ()) ;;
         ())
      (fun: <> => ivar_4٠is_set "ivar").
