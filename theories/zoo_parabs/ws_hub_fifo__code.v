Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.waiters.
Require Import zoo_saturn.mpmc_queue_1.
Require Import zoo_parabs.ws_hub_fifo__types.
Require Import zoo.options.

Definition ws_hub_fifo٠create : val :=
  fun: "sz" =>
    { "sz", mpmc_queue_1٠create (), waiters٠create "sz", "sz" + 1 }.

Definition ws_hub_fifo٠size : val :=
  fun: "t" =>
    "t".{size}.

Definition ws_hub_fifo٠begin_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] (-1) ;;
    ().

Definition ws_hub_fifo٠end_inactive : val :=
  fun: "t" =>
    FAA "t".[num_active] 1 ;;
    ().

Definition ws_hub_fifo٠block : val :=
  fun: "t" "_i" =>
    ws_hub_fifo٠begin_inactive "t".

Definition ws_hub_fifo٠unblock : val :=
  fun: "t" "_i" =>
    ws_hub_fifo٠end_inactive "t".

Definition ws_hub_fifo٠closed : val :=
  fun: "t" =>
    "t".{num_active} == 0.

Definition ws_hub_fifo٠notify : val :=
  fun: "t" =>
    waiters٠notify_one "t".{waiters}.

Definition ws_hub_fifo٠notify_all : val :=
  fun: "t" =>
    waiters٠notify_all "t".{waiters}.

Definition ws_hub_fifo٠push : val :=
  fun: "t" "_i" "v" =>
    mpmc_queue_1٠push "t".{queue} "v" ;;
    ws_hub_fifo٠notify "t".

Definition ws_hub_fifo٠pop' : val :=
  fun: "t" =>
    mpmc_queue_1٠pop "t".{queue}.

Definition ws_hub_fifo٠pop : val :=
  fun: "t" "_i" =>
    ws_hub_fifo٠pop' "t".

Definition ws_hub_fifo٠steal_aux : val :=
  rec: "steal_aux" "t" "i" "notification" "pred" =>
    waiters٠prepare_wait "t".{waiters} "i" ;;
    "notification" (fun: <> => waiters٠notify "t".{waiters} "i") ;;
    if: "pred" () then (
      if: ~ waiters٠cancel_wait "t".{waiters} "i" then (
        waiters٠notify_one "t".{waiters}
      ) else (
        ()
      ) ;;
      §None
    ) else (
      match: ws_hub_fifo٠pop' "t" with
      | Some <> as "res" =>
          waiters٠cancel_wait "t".{waiters} "i" ;;
          "res"
      | None =>
          waiters٠commit_wait "t".{waiters} "i" ;;
          "steal_aux" "t" "i" (fun: <> => ()) "pred"
      end
    ).

Definition ws_hub_fifo٠steal_until : val :=
  fun: "t" "i" <> <> "notification" "pred" =>
    ws_hub_fifo٠steal_aux "t" "i" "notification" "pred".

Definition ws_hub_fifo٠steal : val :=
  fun: "t" "i" <> <> =>
    ws_hub_fifo٠begin_inactive "t" ;;
    let: "res" :=
      ws_hub_fifo٠steal_aux
        "t"
        "i"
        (fun: <> => ())
        (fun: <> => ws_hub_fifo٠closed "t")
    in
    match: "res" with
    | None =>
        ws_hub_fifo٠notify_all "t"
    | Some <> =>
        ws_hub_fifo٠end_inactive "t"
    end ;;
    "res".

Definition ws_hub_fifo٠close : val :=
  ws_hub_fifo٠begin_inactive.

Definition ws_hub_fifo٠pop_steal_until : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" "notification" "pred" =>
    if: "pred" () then (
      §None
    ) else (
      match: ws_hub_fifo٠pop "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub_fifo٠steal_until
            "t"
            "i"
            "max_round_noyield"
            "max_round_yield"
            "notification"
            "pred"
      end
    ).

Definition ws_hub_fifo٠pop_steal : val :=
  fun: "t" "i" "max_round_noyield" "max_round_yield" =>
    match: ws_hub_fifo٠pop "t" "i" with
    | Some <> as "res" =>
        "res"
    | None =>
        ws_hub_fifo٠steal "t" "i" "max_round_noyield" "max_round_yield"
    end.
