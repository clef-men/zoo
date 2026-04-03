(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

type 'a t =
  { queues: 'a Ws_deques_public.t
  ; rounds: Random_round.t array
  ; all_waiters: Waiter.t array
  ; waiters: Waiters.t
  ; mutable killed: bool [@atomic]
  }

let create sz =
  { queues= Ws_deques_public.create sz
  ; rounds= Array.unsafe_init sz (fun _ -> Random_round.create @@ Int.positive_part @@ sz - 1)
  ; all_waiters= Array.unsafe_init sz Waiter.create
  ; waiters= Waiters.create ()
  ; killed= false
  }

let size t =
  Array.size t.rounds

let block t i =
  Ws_deques_public.block t.queues i

let unblock t i =
  Ws_deques_public.unblock t.queues i

let killed t =
  t.killed

let push t i v =
  Ws_deques_public.push t.queues i v ;
  Waiters.notify_one t.waiters

let pop t i =
  Ws_deques_public.pop t.queues i

let try_steal_once t i =
  let round = Array.unsafe_get t.rounds i in
  Random_round.reset round ;
  Ws_deques_public.steal_as t.queues i round

let rec try_steal t i yield max_round pred =
  if max_round <= 0 then
    Optional.Nothing
  else
    match try_steal_once t i with
    | Some v ->
        Optional.Something v
    | None ->
        if pred () then
          Optional.Anything
        else (
          if yield then
            Domain.yield () ;
          try_steal t i yield (max_round - 1) pred
        )
let try_steal t i max_round_noyield max_round_yield pred =
  match try_steal t i false max_round_noyield pred with
  | Optional.Something _ as res ->
      res
  | Anything ->
      Anything
  | Nothing ->
      try_steal t i true max_round_yield pred

let rec steal_aux t i max_round_noyield max_round_yield ~finished ~prepare_sleep =
  match try_steal t i max_round_noyield max_round_yield finished with
  | Optional.Something v ->
      Some v
  | Anything ->
      None
  | Nothing ->
      let waiter = t.all_waiters.(i) in
      Waiter.prepare waiter;
      Waiters.push t.waiters waiter;
      match try_steal_once t i with
      | Some _ as res ->
        (* We are stealing a task that notified someone
           so they will have a spurious wakeup. *)
        ignore (Waiter.cancel waiter);
        res
      | None ->
        prepare_sleep (fun () -> ignore (Waiter.notify waiter));
        if finished () then (
          begin match Waiter.cancel waiter with
          | Already_notified -> Waiters.notify_one t.waiters
          | First -> ()
          end;
          None
        ) else (
          Waiter.commit waiter;
          steal_aux t i max_round_noyield max_round_yield ~finished ~prepare_sleep
        )

let steal_until t i max_round_noyield max_round_yield ~finished ~prepare_sleep =
  block t i ;
  let res =
    steal_aux t i max_round_noyield max_round_yield
      ~finished ~prepare_sleep
  in
  unblock t i ;
  res

let steal t i max_round_noyield max_round_yield =
  block t i ;
  let res =
    steal_aux t i max_round_noyield max_round_yield
      ~finished:(fun () -> killed t) ~prepare_sleep:ignore
  in
  unblock t i ;
  res

let kill t =
  t.killed <- true ;
  Waiters.notify_all t.waiters

let pop_steal_until t i max_round_noyield max_round_yield ~finished ~prepare_sleep =
  if finished () then
    None
  else
    match pop t i with
    | Some _ as res ->
        res
    | None ->
        steal_until t i max_round_noyield max_round_yield ~finished ~prepare_sleep

let pop_steal t i max_round_noyield max_round_yield =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal t i max_round_noyield max_round_yield
