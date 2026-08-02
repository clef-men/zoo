Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_hub_std.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_std.ivar_4.
Require Import zoo_parabs.pool__types.
Require Import zoo.options.

Definition pool٠max_round_noyield : val :=
  1024.

Definition pool٠max_round_yield : val :=
  32.

Definition pool٠context : val :=
  𝗳𝘂𝗻 "sz" "hub" "id" ->
    ("sz", "hub", "id").

Definition pool٠context_main : val :=
  𝗳𝘂𝗻 "t" ->
    pool٠context "t".{size} "t".{hub} 0.

Definition pool٠execute : val :=
  𝗳𝘂𝗻 "ctx" "job" ->
    "job" "ctx".

Definition pool٠worker : val :=
  𝗿𝗲𝗰 "worker" "ctx" ->
    𝗺𝗮𝘁𝗰𝗵
      ws_hub_std٠pop_steal
        "ctx".<context_hub>
        "ctx".<context_id>
        pool٠max_round_noyield
        pool٠max_round_yield
    𝘄𝗶𝘁𝗵
    | None ->
        ()
    | Some "job" ->
        pool٠execute "ctx" "job" ⍮
        "worker" "ctx"
    𝗲𝗻𝗱.

Definition pool٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    𝗹𝗲𝘁 "hub" = ws_hub_std٠create ("sz" + 1) 𝗶𝗻
    ws_hub_std٠block "hub" 0 ⍮
    𝗹𝗲𝘁 "domains" =
      array٠unsafe_initi
        "sz"
        (𝗳𝘂𝗻 "i" ->
           domain٠spawn
             (𝗳𝘂𝗻 ⎽ ->
                pool٠worker (pool٠context "sz" "hub" ("i" + 1))))
    𝗶𝗻
    { "sz", "hub", "domains", () }.

Definition pool٠run_on : val :=
  𝗳𝘂𝗻 "t" "task" ->
    ws_hub_std٠unblock "t".{hub} 0 ⍮
    𝗹𝗲𝘁 "res" =
      pool٠execute (pool٠context_main "t") "task"
    𝗶𝗻
    ws_hub_std٠block "t".{hub} 0 ⍮
    "res".

Definition pool٠close : val :=
  𝗳𝘂𝗻 "t" ->
    ws_hub_std٠close "t".{hub} ⍮
    ws_hub_std٠unblock "t".{hub} 0 ⍮
    pool٠worker (pool٠context_main "t") ⍮
    array٠iter domain٠join "t".{domains}.

Definition pool٠run : val :=
  𝗳𝘂𝗻 "num_worker" "task" ->
    𝗹𝗲𝘁 "t" = pool٠create "num_worker" 𝗶𝗻
    𝗹𝗲𝘁 "res" = pool٠run_on "t" "task" 𝗶𝗻
    pool٠close "t" ⍮
    "res".

Definition pool٠size : val :=
  𝗳𝘂𝗻 "ctx" ->
    "ctx".<context_size>.

Definition pool٠async : val :=
  𝗳𝘂𝗻 "ctx" "task" ->
    ws_hub_std٠push "ctx".<context_hub> "ctx".<context_id> "task".

Definition pool٠wait₁ : val :=
  𝗿𝗲𝗰 "wait" "ctx" "notification" "pred" ->
    𝗺𝗮𝘁𝗰𝗵
      ws_hub_std٠pop_steal_until
        "ctx".<context_hub>
        "ctx".<context_id>
        pool٠max_round_noyield
        pool٠max_round_yield
        "notification"
        "pred"
    𝘄𝗶𝘁𝗵
    | None ->
        ()
    | Some "job" ->
        pool٠execute "ctx" "job" ⍮
        "wait" "ctx" "notification" "pred"
    𝗲𝗻𝗱.

Definition pool٠wait : val :=
  𝗳𝘂𝗻 "ctx" "notification" "pred" ->
    𝗹𝗲𝘁 "notification_registered" = 𝗿𝗲𝗳 false 𝗶𝗻
    𝗹𝗲𝘁 "notification" "notify" =
      𝗶𝗳 ~ !"notification_registered" 𝘁𝗵𝗲𝗻 (
        "notification_registered" <- true ⍮
        "notification" "notify"
      )
    𝗶𝗻
    pool٠wait₁ "ctx" "notification" "pred".

Definition pool٠wait_ivar : val :=
  𝗳𝘂𝗻 "ctx" "ivar" ->
    pool٠wait
      "ctx"
      (𝗳𝘂𝗻 "notify" ->
         ivar_4٠wait "ivar" (𝗳𝘂𝗻 "_ctx" "_v" -> "notify" ()) ⍮
         ())
      (𝗳𝘂𝗻 ⎽ -> ivar_4٠is_set "ivar").
