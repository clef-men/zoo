Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.ws_bdeques_public.
Require Import zoo_parabs.waiters.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo_std.array.
Require Import zoo_std.random_round.
Require Import zoo_std.optional.
Require Import zoo_std.int.
Require Import zoo_std.domain.
Require Import zoo_parabs.ws_hub_hybrid__types.
Require Import zoo.options.

Definition ws_hub_hybrid٠create : val :=
  fun: "sz" =>
    { ws_bdeques_public٠create "sz",
      array٠unsafe_init
        "sz"
        (fun: <> => random_round٠create (int٠positive_part ("sz" - 1))),
      mpmc_queue_1٠create (),
      waiters٠create "sz",
      "sz" + 1
    }.

Definition ws_hub_hybrid٠size : val :=
  fun: "t" =>
    array٠size "t".{rounds}.

Definition ws_hub_hybrid٠begin_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] (-1) ;;
    ().

Definition ws_hub_hybrid٠end_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] 1 ;;
    ().

Definition ws_hub_hybrid٠block_active : val :=
  fun: "t" "i" =>
    ws_bdeques_public٠block "t".{deques} "i".

Definition ws_hub_hybrid٠unblock_active : val :=
  fun: "t" "i" =>
    ws_bdeques_public٠unblock "t".{deques} "i".

Definition ws_hub_hybrid٠block : val :=
  fun: "t" "i" =>
    ws_hub_hybrid٠begin_inactive "t" ;;
    ws_hub_hybrid٠block_active "t" "i".

Definition ws_hub_hybrid٠unblock : val :=
  fun: "t" "i" =>
    ws_hub_hybrid٠unblock_active "t" "i" ;;
    ws_hub_hybrid٠end_inactive "t".

Definition ws_hub_hybrid٠closed : val :=
  fun: "t" =>
    "t".{num_active} == 0.

Definition ws_hub_hybrid٠notify : val :=
  fun: "t" =>
    waiters٠notify_one "t".{waiters}.

Definition ws_hub_hybrid٠notify_all : val :=
  fun: "t" =>
    waiters٠notify_all "t".{waiters}.

Definition ws_hub_hybrid٠push : val :=
  fun: "t" "i" "v" =>
    if: ~ ws_bdeques_public٠push "t".{deques} "i" "v" then (
      mpmc_queue_1٠push "t".{queue} "v"
    ) else (
      ()
    ) ;;
    ws_hub_hybrid٠notify "t".

Definition ws_hub_hybrid٠pop : val :=
  fun: "t" "i" =>
    match: ws_bdeques_public٠pop "t".{deques} "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        mpmc_queue_1٠pop "t".{queue}
    end.

Definition ws_hub_hybrid٠try_steal_once : val :=
  fun: "t" "i" =>
    let: "round" := array٠unsafe_get "t".{rounds} "i" in
    random_round٠reset "round" ;;
    ws_bdeques_public٠steal_as "t".{deques} "i" "round".

Definition ws_hub_hybrid٠try_steal₀ : val :=
  rec: "try_steal" "t" "i" "yield" "max_round" "pred" =>
    if: "max_round" ≤ 0 then (
      §Nothing
    ) else (
      match: ws_hub_hybrid٠try_steal_once "t" "i" with
      | Some "v" =>
          ‘Something( "v" )
      | None =>
          if: "pred" () then (
            §Anything
          ) else (
            if: "yield" then (
              domain٠yield ()
            ) else (
              ()
            ) ;;
            "try_steal" "t" "i" "yield" ("max_round" - 1) "pred"
          )
      end
    ).

Definition ws_hub_hybrid٠try_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "pred" =>
    match:
      ws_hub_hybrid٠try_steal₀ "t" "i" false "max_round_noyield" "pred"
    with
    | Something <> as "res" =>
        "res"
    | Anything =>
        §Anything
    | Nothing =>
        ws_hub_hybrid٠try_steal₀ "t" "i" true "max_round_yield" "pred"
    end.

Definition ws_hub_hybrid٠steal_aux : val :=
  rec: "steal_aux" "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    match:
      ws_hub_hybrid٠try_steal
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        "pred"
    with
    | Something "v" =>
        ‘Some( "v" )
    | Anything =>
        §None
    | Nothing =>
        waiters٠prepare_wait "t".{waiters} "i" ;;
        match: ws_hub_hybrid٠try_steal_once "t" "i" with
        | Some <> as "res" =>
            waiters٠cancel_wait "t".{waiters} "i" ;;
            "res"
        | None =>
            "notification" (fun: <> => waiters٠notify "t".{waiters} "i") ;;
            if: "pred" () then (
              if: ~ waiters٠cancel_wait "t".{waiters} "i" then (
                waiters٠notify_one "t".{waiters}
              ) else (
                ()
              ) ;;
              §None
            ) else (
              waiters٠commit_wait "t".{waiters} "i" ;;
              "steal_aux"
                "t"
                "i"
                "max_round_noyield"
                "max_round_yield"
                (fun: <> => ())
                "pred"
            )
        end
    end.

Definition ws_hub_hybrid٠steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    ws_hub_hybrid٠block_active "t" "i" ;;
    let: "res" :=
      ws_hub_hybrid٠steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        "notification"
        "pred"
    in
    ws_hub_hybrid٠unblock_active "t" "i" ;;
    "res".

Definition ws_hub_hybrid٠steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    ws_hub_hybrid٠block "t" "i" ;;
    let: "res" :=
      ws_hub_hybrid٠steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        (fun: <> => ())
        (fun: <> => ws_hub_hybrid٠closed "t")
    in
    match: "res" with
    | None =>
        ws_hub_hybrid٠notify_all "t"
    | Some <> =>
        ws_hub_hybrid٠unblock "t" "i"
    end ;;
    "res".

Definition ws_hub_hybrid٠close : val :=
  ws_hub_hybrid٠begin_inactive.

Definition ws_hub_hybrid٠pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    if: "pred" () then (
      §None
    ) else (
      match: ws_hub_hybrid٠pop "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_hybrid٠steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      end
    ).

Definition ws_hub_hybrid٠pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_hybrid٠pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_hybrid٠steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
