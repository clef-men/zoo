Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_deques_public.
Require Import zoo_parabs.waiters.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_std.optional.
Require Import zoo_std.int.
Require Import zoo_std.domain.
Require Import zoo_parabs.ws_hub_std__types.
Require Import zoo.options.

Definition ws_hub_std٠create : val :=
  𝗳𝘂𝗻 "sz" ->
    { ws_deques_public٠create "sz",
      array٠unsafe_init
        "sz"
        (𝗳𝘂𝗻 ⎽ ->
           random_round٠create (int٠positive_part ("sz" - 1))),
      waiters٠create "sz",
      "sz" + 1
    }.

Definition ws_hub_std٠size : val :=
  𝗳𝘂𝗻 "t" ->
    array٠size "t".{rounds}.

Definition ws_hub_std٠begin_inactive : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[num_active] (-1) ⍮
    ().

Definition ws_hub_std٠end_inactive : val :=
  𝗳𝘂𝗻 "t" ->
    𝗳𝗮𝗮 "t".[num_active] 1 ⍮
    ().

Definition ws_hub_std٠block_active : val :=
  𝗳𝘂𝗻 "t" "i" ->
    ws_deques_public٠block "t".{deques} "i".

Definition ws_hub_std٠unblock_active : val :=
  𝗳𝘂𝗻 "t" "i" ->
    ws_deques_public٠unblock "t".{deques} "i".

Definition ws_hub_std٠block : val :=
  𝗳𝘂𝗻 "t" "i" ->
    ws_hub_std٠begin_inactive "t" ⍮
    ws_hub_std٠block_active "t" "i".

Definition ws_hub_std٠unblock : val :=
  𝗳𝘂𝗻 "t" "i" ->
    ws_hub_std٠unblock_active "t" "i" ⍮
    ws_hub_std٠end_inactive "t".

Definition ws_hub_std٠closed : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{num_active} == 0.

Definition ws_hub_std٠notify : val :=
  𝗳𝘂𝗻 "t" ->
    waiters٠notify_one "t".{waiters}.

Definition ws_hub_std٠notify_all : val :=
  𝗳𝘂𝗻 "t" ->
    waiters٠notify_all "t".{waiters}.

Definition ws_hub_std٠push : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    ws_deques_public٠push "t".{deques} "i" "v" ⍮
    ws_hub_std٠notify "t".

Definition ws_hub_std٠pop : val :=
  𝗳𝘂𝗻 "t" "i" ->
    ws_deques_public٠pop "t".{deques} "i".

Definition ws_hub_std٠try_steal_once : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗲𝘁 "round" = array٠unsafe_get "t".{rounds} "i" 𝗶𝗻
    random_round٠reset "round" ⍮
    ws_deques_public٠steal_as "t".{deques} "i" "round".

Definition ws_hub_std٠try_steal₀ : val :=
  𝗿𝗲𝗰 "try_steal" "t" "i" "yield" "max_round" "pred" ->
    𝗶𝗳 "max_round" ≤ 0 𝘁𝗵𝗲𝗻 (
      §Nothing
    ) 𝗲𝗹𝘀𝗲 (
      𝗺𝗮𝘁𝗰𝗵
        ws_hub_std٠try_steal_once "t" "i"
      𝘄𝗶𝘁𝗵
      | Some "v" ->
          ‘Something( "v" )
      | None ->
          𝗶𝗳 "pred" () 𝘁𝗵𝗲𝗻 (
            §Anything
          ) 𝗲𝗹𝘀𝗲 (
            𝗶𝗳 "yield" 𝘁𝗵𝗲𝗻 (
              domain٠yield ()
            ) 𝗲𝗹𝘀𝗲 (
              ()
            ) ⍮
            "try_steal" "t" "i" "yield" ("max_round" - 1) "pred"
          )
      𝗲𝗻𝗱
    ).

Definition ws_hub_std٠try_steal : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" "pred" ->
    𝗺𝗮𝘁𝗰𝗵
      ws_hub_std٠try_steal₀ "t" "i" false "max_round_noyield" "pred"
    𝘄𝗶𝘁𝗵
    | Something ⎽ 𝗮𝘀 "res" ->
        "res"
    | Anything ->
        §Anything
    | Nothing ->
        ws_hub_std٠try_steal₀ "t" "i" true "max_round_yield" "pred"
    𝗲𝗻𝗱.

Definition ws_hub_std٠steal_aux : val :=
  𝗿𝗲𝗰 "steal_aux" "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" ->
    𝗺𝗮𝘁𝗰𝗵
      ws_hub_std٠try_steal
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        "pred"
    𝘄𝗶𝘁𝗵
    | Something "v" ->
        ‘Some( "v" )
    | Anything ->
        §None
    | Nothing ->
        waiters٠prepare_wait "t".{waiters} "i" ⍮
        𝗺𝗮𝘁𝗰𝗵
          ws_hub_std٠try_steal_once "t" "i"
        𝘄𝗶𝘁𝗵
        | Some ⎽ 𝗮𝘀 "res" ->
            waiters٠cancel_wait "t".{waiters} "i" ⍮
            "res"
        | None ->
            "notification"
              (𝗳𝘂𝗻 ⎽ -> waiters٠notify "t".{waiters} "i") ⍮
            𝗶𝗳 "pred" () 𝘁𝗵𝗲𝗻 (
              𝗶𝗳
                ~ waiters٠cancel_wait "t".{waiters} "i"
              𝘁𝗵𝗲𝗻 (
                waiters٠notify_one "t".{waiters}
              ) 𝗲𝗹𝘀𝗲 (
                ()
              ) ⍮
              §None
            ) 𝗲𝗹𝘀𝗲 (
              waiters٠commit_wait "t".{waiters} "i" ⍮
              "steal_aux"
                "t"
                "i"
                "max_round_noyield"
                "max_round_yield"
                (𝗳𝘂𝗻 ⎽ -> ())
                "pred"
            )
        𝗲𝗻𝗱
    𝗲𝗻𝗱.

Definition ws_hub_std٠steal_until : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" ->
    ws_hub_std٠block_active "t" "i" ⍮
    𝗹𝗲𝘁 "res" =
      ws_hub_std٠steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        "notification"
        "pred"
    𝗶𝗻
    ws_hub_std٠unblock_active "t" "i" ⍮
    "res".

Definition ws_hub_std٠steal : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" ->
    ws_hub_std٠block "t" "i" ⍮
    𝗹𝗲𝘁 "res" =
      ws_hub_std٠steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        (𝗳𝘂𝗻 ⎽ -> ())
        (𝗳𝘂𝗻 ⎽ -> ws_hub_std٠closed "t")
    𝗶𝗻
    𝗺𝗮𝘁𝗰𝗵 "res" 𝘄𝗶𝘁𝗵
    | None ->
        ws_hub_std٠notify_all "t"
    | Some ⎽ ->
        ws_hub_std٠unblock "t" "i"
    𝗲𝗻𝗱 ⍮
    "res".

Definition ws_hub_std٠close : val :=
  ws_hub_std٠begin_inactive.

Definition ws_hub_std٠pop_steal_until : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" ->
    𝗶𝗳 "pred" () 𝘁𝗵𝗲𝗻 (
      §None
    ) 𝗲𝗹𝘀𝗲 (
      𝗺𝗮𝘁𝗰𝗵 ws_hub_std٠pop "t" "i" 𝘄𝗶𝘁𝗵
      | Some ⎽ 𝗮𝘀 "res" ->
          "res"
      | None ->
          ws_hub_std٠steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      𝗲𝗻𝗱
    ).

Definition ws_hub_std٠pop_steal : val :=
  𝗳𝘂𝗻 "t" "i" "max_round_noyield" "max_round_yield" ->
    𝗺𝗮𝘁𝗰𝗵 ws_hub_std٠pop "t" "i" 𝘄𝗶𝘁𝗵
    | Some ⎽ 𝗮𝘀 "res" ->
        "res"
    | None ->
        ws_hub_std٠steal "t" "i" "max_round_noyield" "max_round_yield"
    𝗲𝗻𝗱.
