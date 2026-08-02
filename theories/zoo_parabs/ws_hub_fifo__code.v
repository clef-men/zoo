Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.waiters.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo.options.

Notation "'ws_hub_fifo٠size'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 0
)(in custom zoo_field
).
Notation "'ws_hub_fifo٠queue'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 1
)(in custom zoo_field
).
Notation "'ws_hub_fifo٠waiters'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 2
)(in custom zoo_field
).
Notation "'ws_hub_fifo٠num_active'" := (
  in_type "zoo_parabs.ws_hub_fifo.t" 3
)(in custom zoo_field
).

Definition ws_hub_fifo٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { "sz", mpmc_queue_1٠create (), waiters٠create "sz", "sz" + 1 }.

Definition ws_hub_fifo٠size : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{ws_hub_fifo٠size}.

Definition ws_hub_fifo٠begin_inactive : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[ws_hub_fifo٠num_active] (-1) ⍮
    ().

Definition ws_hub_fifo٠end_inactive : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[ws_hub_fifo٠num_active] 1 ⍮
    ().

Definition ws_hub_fifo٠block : val :=
  𝗳𝘂𝗻 "t" "_i" ->
    ws_hub_fifo٠begin_inactive "t".

Definition ws_hub_fifo٠unblock : val :=
  𝗳𝘂𝗻 "t" "_i" ->
    ws_hub_fifo٠end_inactive "t".

Definition ws_hub_fifo٠closed : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{ws_hub_fifo٠num_active} == 0.

Definition ws_hub_fifo٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    waiters٠notify_one "t".{ws_hub_fifo٠waiters}.

Definition ws_hub_fifo٠notify_all : val :=
  𝗳𝘂𝗻 "t" ->
    waiters٠notify_all "t".{ws_hub_fifo٠waiters}.

Definition ws_hub_fifo٠push : val :=
  𝗳𝘂𝗻 "t" "_i" "v" ->
    mpmc_queue_1٠push "t".{ws_hub_fifo٠queue} "v" ⍮
    ws_hub_fifo٠notify "t".

Definition ws_hub_fifo٠pop' : val :=
  𝗳𝘂𝗻 "t" ->
    mpmc_queue_1٠pop "t".{ws_hub_fifo٠queue}.

Definition ws_hub_fifo٠pop : val :=
  𝗳𝘂𝗻 "t" "_i" ->
    ws_hub_fifo٠pop' "t".

Definition ws_hub_fifo٠steal_aux : val :=
  𝗿𝗲𝗰 "steal_aux" "t" "i" "notification" "pred" ->
    waiters٠prepare_wait "t".{ws_hub_fifo٠waiters} "i" ⍮
    "notification"
      (𝗳𝘂𝗻 ⎽ -> waiters٠notify "t".{ws_hub_fifo٠waiters} "i") ⍮
    𝗶𝗳 "pred" () 𝘁𝗵𝗲𝗻 (
      𝗶𝗳
        ~ waiters٠cancel_wait "t".{ws_hub_fifo٠waiters} "i"
      𝘁𝗵𝗲𝗻 (
        waiters٠notify_one "t".{ws_hub_fifo٠waiters}
      ) 𝗲𝗹𝘀𝗲 (
        ()
      ) ⍮
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗺𝗮𝘁𝗰𝗵 ws_hub_fifo٠pop' "t" 𝘄𝗶𝘁𝗵
      | Some ⎽ 𝗮𝘀 "res" ->
          waiters٠cancel_wait "t".{ws_hub_fifo٠waiters} "i" ⍮
          "res"
      | None ->
          waiters٠commit_wait "t".{ws_hub_fifo٠waiters} "i" ⍮
          "steal_aux" "t" "i" (𝗳𝘂𝗻 ⎽ -> ()) "pred"
      𝗲𝗻𝗱
    ).

Definition ws_hub_fifo٠steal_until : val :=
  𝗳𝘂𝗻 "t" "i" ⎽ ⎽ "notification" "pred" ->
    ws_hub_fifo٠steal_aux "t" "i" "notification" "pred".

Definition ws_hub_fifo٠steal : val :=
  𝗳𝘂𝗻 "t" "i" ⎽ ⎽ ->
    ws_hub_fifo٠begin_inactive "t" ⍮
    𝗹𝗲𝘁 "res" =
      ws_hub_fifo٠steal_aux
        "t"
        "i"
        (𝗳𝘂𝗻 ⎽ -> ())
        (𝗳𝘂𝗻 ⎽ -> ws_hub_fifo٠closed "t")
    𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵 "res" 𝘄𝗶𝘁𝗵
    | None ->
        ws_hub_fifo٠notify_all "t"
    | Some ⎽ ->
        ws_hub_fifo٠end_inactive "t"
    𝗲𝗻𝗱 ⍮
    "res".

Definition ws_hub_fifo٠close : val :=
  ws_hub_fifo٠begin_inactive.

Definition ws_hub_fifo٠pop_steal_until : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" ->
    𝗶𝗳 "pred" () 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗺𝗮𝘁𝗰𝗵 ws_hub_fifo٠pop "t" "i" 𝘄𝗶𝘁𝗵
      | Some ⎽ 𝗮𝘀 "res" ->
          "res"
      | None ->
          ws_hub_fifo٠steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      𝗲𝗻𝗱
    ).

Definition ws_hub_fifo٠pop_steal : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" ->
    𝗺𝗮𝘁𝗰𝗵 ws_hub_fifo٠pop "t" "i" 𝘄𝗶𝘁𝗵
    | Some ⎽ 𝗮𝘀 "res" ->
        "res"
    | None ->
        ws_hub_fifo٠steal "t" "i" "max_round_noyield" "max_round_yield"
    𝗲𝗻𝗱.
