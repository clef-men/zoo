From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  ws_deques_public
  waiters.
From zoo_std Require Import
  array
  random_round
  optional
  int
  domain.
From zoo_parabs Require Import
  ws_hub_std__types.
From zoo Require Import
  options.

Definition ws_hub_std_create : val :=
  fun: "sz" =>
    { ws_deques_public_create "sz",
      array_unsafe_init
        "sz"
        (fun: <> => random_round_create (int_positive_part ("sz" - 1))),
      waiters_create "sz",
      "sz" + 1
    }.

Definition ws_hub_std_size : val :=
  fun: "t" =>
    array_size "t".{rounds}.

Definition ws_hub_std_begin_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] (-1) ;;
    ().

Definition ws_hub_std_end_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] 1 ;;
    ().

Definition ws_hub_std_block_active : val :=
  fun: "t" "i" =>
    ws_deques_public_block "t".{queues} "i".

Definition ws_hub_std_unblock_active : val :=
  fun: "t" "i" =>
    ws_deques_public_unblock "t".{queues} "i".

Definition ws_hub_std_block : val :=
  fun: "t" "i" =>
    ws_hub_std_begin_inactive "t" ;;
    ws_hub_std_block_active "t" "i".

Definition ws_hub_std_unblock : val :=
  fun: "t" "i" =>
    ws_hub_std_unblock_active "t" "i" ;;
    ws_hub_std_end_inactive "t".

Definition ws_hub_std_closed : val :=
  fun: "t" =>
    "t".{num_active} == 0.

Definition ws_hub_std_notify : val :=
  fun: "t" =>
    waiters_notify_one "t".{waiters}.

Definition ws_hub_std_notify_all : val :=
  fun: "t" =>
    waiters_notify_all "t".{waiters}.

Definition ws_hub_std_push : val :=
  fun: "t" "i" "v" =>
    ws_deques_public_push "t".{queues} "i" "v" ;;
    ws_hub_std_notify "t".

Definition ws_hub_std_pop : val :=
  fun: "t" "i" =>
    ws_deques_public_pop "t".{queues} "i".

Definition ws_hub_std_try_steal_once : val :=
  fun: "t" "i" =>
    let: "round" := array_unsafe_get "t".{rounds} "i" in
    random_round_reset "round" ;;
    ws_deques_public_steal_as "t".{queues} "i" "round".

Definition ws_hub_std_try_steal₀ : val :=
  rec: "try_steal" "t" "i" "yield" "max_round" "pred" =>
    if: "max_round" ≤ 0 then (
      §Nothing
    ) else (
      match: ws_hub_std_try_steal_once "t" "i" with
      | Some "v" =>
          ‘Something( "v" )
      | None =>
          if: "pred" () then (
            §Anything
          ) else (
            if: "yield" then (
              domain_yield ()
            ) else (
              ()
            ) ;;
            "try_steal" "t" "i" "yield" ("max_round" - 1) "pred"
          )
      end
    ).

Definition ws_hub_std_try_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "pred" =>
    match:
      ws_hub_std_try_steal₀ "t" "i" false "max_round_noyield" "pred"
    with
    | Something <> as "res" =>
        "res"
    | Anything =>
        §Anything
    | Nothing =>
        ws_hub_std_try_steal₀ "t" "i" true "max_round_yield" "pred"
    end.

Definition ws_hub_std_steal_aux : val :=
  rec: "steal_aux" "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    match:
      ws_hub_std_try_steal
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
        waiters_prepare_wait "t".{waiters} "i" ;;
        match: ws_hub_std_try_steal_once "t" "i" with
        | Some <> as "res" =>
            waiters_cancel_wait "t".{waiters} "i" ;;
            "res"
        | None =>
            "notification" (fun: <> => waiters_notify "t".{waiters} "i") ;;
            if: "pred" () then (
              if: ~ waiters_cancel_wait "t".{waiters} "i" then (
                waiters_notify_one "t".{waiters}
              ) else (
                ()
              ) ;;
              §None
            ) else (
              waiters_commit_wait "t".{waiters} "i" ;;
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

Definition ws_hub_std_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    ws_hub_std_block_active "t" "i" ;;
    let: "res" :=
      ws_hub_std_steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        "notification"
        "pred"
    in
    ws_hub_std_unblock_active "t" "i" ;;
    "res".

Definition ws_hub_std_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    ws_hub_std_block "t" "i" ;;
    let: "res" :=
      ws_hub_std_steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        (fun: <> => ())
        (fun: <> => ws_hub_std_closed "t")
    in
    match: "res" with
    | None =>
        ws_hub_std_notify_all "t"
    | Some <> =>
        ws_hub_std_unblock "t" "i"
    end ;;
    "res".

Definition ws_hub_std_close : val :=
  ws_hub_std_begin_inactive.

Definition ws_hub_std_pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    if: "pred" () then (
      §None
    ) else (
      match: ws_hub_std_pop "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_std_steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      end
    ).

Definition ws_hub_std_pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_std_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_std_steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
