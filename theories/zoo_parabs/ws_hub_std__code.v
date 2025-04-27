From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array
  random_round
  optional
  int
  domain.
From zoo_parabs Require Import
  ws_queues_public
  waiters.
From zoo_parabs Require Import
  ws_hub_std__types.
From zoo Require Import
  options.

Definition ws_hub_std_create : val :=
  fun: "sz" =>
    { ws_queues_public_create "sz",
      array_unsafe_init
        "sz"
        (fun: <> => random_round_create (int_positive_part ("sz" - #1))),
      waiters_create (),
      #false
    }.

Definition ws_hub_std_size : val :=
  fun: "t" =>
    array_size "t".{rounds}.

Definition ws_hub_std_block : val :=
  fun: "t" "i" =>
    ws_queues_public_block "t".{queues} "i".

Definition ws_hub_std_unblock : val :=
  fun: "t" "i" =>
    ws_queues_public_unblock "t".{queues} "i".

Definition ws_hub_std_killed : val :=
  fun: "t" =>
    "t".{killed}.

Definition ws_hub_std_notify : val :=
  fun: "t" =>
    waiters_notify "t".{waiters}.

Definition ws_hub_std_notify_all : val :=
  fun: "t" =>
    waiters_notify_many "t".{waiters} (ws_hub_std_size "t").

Definition ws_hub_std_push : val :=
  fun: "t" "i" "v" =>
    ws_queues_public_push "t".{queues} "i" "v" ;;
    ws_hub_std_notify "t".

Definition ws_hub_std_pop : val :=
  fun: "t" "i" =>
    ws_queues_public_pop "t".{queues} "i".

Definition ws_hub_std_try_steal_once : val :=
  fun: "t" "i" =>
    let: "round" := array_unsafe_get "t".{rounds} "i" in
    random_round_reset "round" ;;
    ws_queues_public_steal_as "t".{queues} "i" "round".

Definition ws_hub_std_try_steal : val :=
  rec: "try_steal" "t" "i" "yield" "max_round" "until" =>
    if: "max_round" ≤ #0 then (
      §Nothing
    ) else (
      match: ws_hub_std_try_steal_once "t" "i" with
      | Some "v" =>
          ‘Something( "v" )
      | None =>
          if: "until" () then (
            §Anything
          ) else (
            if: "yield" then (
              domain_yield ()
            ) else (
              ()
            ) ;;
            "try_steal" "t" "i" "yield" ("max_round" - #1) "until"
          )
      end
    ).

Definition ws_hub_std_steal_until_0 : val :=
  rec: "steal_until" "t" "i" "pred" =>
    match: ws_hub_std_try_steal_once "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        if: "pred" () then (
          §None
        ) else (
          domain_yield () ;;
          "steal_until" "t" "i" "pred"
        )
    end.

Definition ws_hub_std_steal_until_1 : val :=
  fun: "t" "i" "max_round_noyield" "pred" =>
    match:
      ws_hub_std_try_steal "t" "i" #false "max_round_noyield" "pred"
    with
    | Something "v" =>
        ‘Some( "v" )
    | Anything =>
        §None
    | Nothing =>
        ws_hub_std_steal_until_0 "t" "i" "pred"
    end.

Definition ws_hub_std_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "pred" =>
    ws_hub_std_block "t" "i" ;;
    let: "res" :=
      ws_hub_std_steal_until_1 "t" "i" "max_round_noyield" "pred"
    in
    ws_hub_std_unblock "t" "i" ;;
    "res".

Definition ws_hub_std_steal_aux : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "until" =>
    match:
      ws_hub_std_try_steal "t" "i" #false "max_round_noyield" "until"
    with
    | Something <> as "res" =>
        "res"
    | Anything =>
        §Anything
    | Nothing =>
        ws_hub_std_try_steal "t" "i" #true "max_round_yield" "until"
    end.

Definition ws_hub_std_steal_0 : val :=
  rec: "steal" "t" "i" "max_round_noyield" "max_round_yield" =>
    match:
      ws_hub_std_steal_aux
        "t"
        "i"
        "max_round_noyield"
        "max_round_yield"
        (fun: <> => ws_hub_std_killed "t")
    with
    | Something "v" =>
        ‘Some( "v" )
    | Anything =>
        §None
    | Nothing =>
        let: "waiters" := "t".{waiters} in
        let: "waiter" := waiters_prepare_wait "waiters" in
        match: ws_hub_std_try_steal_once "t" "i" with
        | Some <> as "res" =>
            waiters_cancel_wait "waiters" "waiter" ;;
            "res"
        | None =>
            if: ws_hub_std_killed "t" then (
              waiters_cancel_wait "waiters" "waiter" ;;
              §None
            ) else (
              waiters_commit_wait "waiters" "waiter" ;;
              "steal" "t" "i" "max_round_noyield" "max_round_yield"
            )
        end
    end.

Definition ws_hub_std_steal : val :=
  fun: "t" "i" "max_round_noyield" "pred" =>
    ws_hub_std_block "t" "i" ;;
    let: "res" := ws_hub_std_steal_0 "t" "i" "max_round_noyield" "pred" in
    ws_hub_std_unblock "t" "i" ;;
    "res".

Definition ws_hub_std_kill : val :=
  fun: "t" =>
    "t" <-{killed} #true ;;
    ws_hub_std_notify_all "t".

Definition ws_hub_std_pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "pred" =>
    match: ws_hub_std_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_std_steal_until "t" "i" "max_round_noyield" "pred"
    end.

Definition ws_hub_std_pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_std_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_std_steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
