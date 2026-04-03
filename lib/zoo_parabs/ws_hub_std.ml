(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

type 'a t =
  { queues: 'a Ws_deques_public.t
  ; rounds: Random_round.t array
  ; waiters: Waiters.t
  ; mutable num_active: int [@atomic]
  }

let create sz =
  { queues= Ws_deques_public.create sz
  ; rounds= Array.unsafe_init sz (fun _ -> Random_round.create @@ Int.positive_part @@ sz - 1)
  ; waiters= Waiters.create sz
  ; num_active= sz + 1
  }

let size t =
  Array.size t.rounds

let begin_inactive t =
  Atomic.Loc.decr [%atomic.loc t.num_active]
let end_inactive t =
  Atomic.Loc.incr [%atomic.loc t.num_active]

let block_active t i =
  Ws_deques_public.block t.queues i
let unblock_active t i =
  Ws_deques_public.unblock t.queues i

let block t i =
  begin_inactive t ;
  block_active t i
let unblock t i =
  unblock_active t i ;
  end_inactive t

let closed t =
  t.num_active == 0

let notify t =
  Waiters.notify t.waiters
let notify_all t =
  Waiters.notify_all t.waiters

let push t i v =
  Ws_deques_public.push t.queues i v ;
  notify t

let pop t i =
  Ws_deques_public.pop t.queues i

let try_steal_once t i =
  let round = Array.unsafe_get t.rounds i in
  Random_round.reset round ;
  Ws_deques_public.steal_as t.queues i round

let rec try_steal t i ~yield ~max_round pred =
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
          try_steal t i ~yield ~max_round:(max_round - 1) pred
        )

let rec steal_until t i pred =
  match try_steal_once t i with
  | Some _ as res ->
      res
  | None ->
      if pred () then (
        None
      ) else (
        Domain.yield () ;
        steal_until t i pred
      )
let steal_until t i ~max_round_noyield pred =
  match try_steal t i ~yield:false ~max_round:max_round_noyield pred with
  | Optional.Something v ->
      Some v
  | Anything ->
      None
  | Nothing ->
      steal_until t i pred
let steal_until t i ~max_round_noyield pred =
  block_active t i ;
  let res = steal_until t i ~max_round_noyield pred in
  unblock_active t i ;
  res

let steal_aux t i ~max_round_noyield ~max_round_yield pred =
  match try_steal t i ~yield:false ~max_round:max_round_noyield pred with
  | Optional.Something _ as res ->
      res
  | Anything ->
      Anything
  | Nothing ->
      try_steal t i ~yield:true ~max_round:max_round_yield pred
let rec steal t i ~max_round_noyield ~max_round_yield =
  match steal_aux t i ~max_round_noyield ~max_round_yield (fun () -> closed t) with
  | Optional.Something v ->
      unblock t i ;
      Some v
  | Anything ->
      notify_all t ;
      None
  | Nothing ->
      let waiter = Waiters.prepare_wait t.waiters i in
      match try_steal_once t i with
      | Some _ as res ->
          Waiters.cancel_wait t.waiters i ;
          unblock t i ;
          res
      | None ->
          if closed t then (
            notify_all t ;
            None
          ) else (
            Waiters.commit_wait t.waiters i waiter ;
            steal t i ~max_round_noyield ~max_round_yield
          )
let steal t i ~max_round_noyield ~max_round_yield =
  block t i ;
  steal t i ~max_round_noyield ~max_round_yield

let close =
  begin_inactive

let pop_steal_until t i ~max_round_noyield pred =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal_until t i ~max_round_noyield pred

let pop_steal t i ~max_round_noyield ~max_round_yield =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal t i ~max_round_noyield ~max_round_yield
