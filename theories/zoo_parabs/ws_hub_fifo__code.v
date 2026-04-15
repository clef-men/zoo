From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_parabs Require Import
  waiters.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Import
  ws_hub_fifo__types.
From zoo Require Import
  options.

Definition ws_hub_fifo_create : val :=
  fun: "sz" =>
    { "sz", mpmc_queue_1_create (), waiters_create "sz", "sz" + 1 }.

Definition ws_hub_fifo_size : val :=
  fun: "t" =>
    "t".{size}.

Definition ws_hub_fifo_begin_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] (-1) ;;
    ().

Definition ws_hub_fifo_end_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] 1 ;;
    ().

Definition ws_hub_fifo_block : val :=
  fun: "t" "_i" =>
    ws_hub_fifo_begin_inactive "t".

Definition ws_hub_fifo_unblock : val :=
  fun: "t" "_i" =>
    ws_hub_fifo_end_inactive "t".

Definition ws_hub_fifo_closed : val :=
  fun: "t" =>
    "t".{num_active} == 0.

Definition ws_hub_fifo_notify : val :=
  fun: "t" =>
    waiters_notify_one "t".{waiters}.

Definition ws_hub_fifo_notify_all : val :=
  fun: "t" =>
    waiters_notify_all "t".{waiters}.

Definition ws_hub_fifo_push : val :=
  fun: "t" "_i" "v" =>
    mpmc_queue_1_push "t".{queue} "v" ;;
    ws_hub_fifo_notify "t".

Definition ws_hub_fifo_pop' : val :=
  fun: "t" =>
    mpmc_queue_1_pop "t".{queue}.

Definition ws_hub_fifo_pop : val :=
  fun: "t" "_i" =>
    ws_hub_fifo_pop' "t".

Definition ws_hub_fifo_steal_aux : val :=
  rec: "steal_aux" "t" "i" "notification" "pred" =>
    waiters_prepare_wait "t".{waiters} "i" ;;
    "notification" (fun: <> => waiters_notify "t".{waiters} "i") ;;
    if: "pred" () then (
      if: ~ waiters_cancel_wait "t".{waiters} "i" then (
        waiters_notify_one "t".{waiters}
      ) else (
        ()
      ) ;;
      §None
    ) else (
      match: ws_hub_fifo_pop' "t" with
      | Some <> as "res" =>
          waiters_cancel_wait "t".{waiters} "i" ;;
          "res"
      | None =>
          waiters_commit_wait "t".{waiters} "i" ;;
          "steal_aux" "t" "i" (fun: <> => ()) "pred"
      end
    ).

Definition ws_hub_fifo_steal_until : val :=
  fun: "t" "i" <> <> "notification" "pred" =>
    ws_hub_fifo_steal_aux "t" "i" "notification" "pred".

Definition ws_hub_fifo_steal : val :=
  fun: "t" "i" <> <> =>
    ws_hub_fifo_begin_inactive "t" ;;
    let: "res" :=
      ws_hub_fifo_steal_aux
        "t"
        "i"
        (fun: <> => ())
        (fun: <> => ws_hub_fifo_closed "t")
    in
    match: "res" with
    | None =>
        ws_hub_fifo_notify_all "t"
    | Some <> =>
        ws_hub_fifo_end_inactive "t"
    end ;;
    "res".

Definition ws_hub_fifo_close : val :=
  ws_hub_fifo_begin_inactive.

Definition ws_hub_fifo_pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    if: "pred" () then (
      §None
    ) else (
      match: ws_hub_fifo_pop "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_fifo_steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      end
    ).

Definition ws_hub_fifo_pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_fifo_pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_fifo_steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
