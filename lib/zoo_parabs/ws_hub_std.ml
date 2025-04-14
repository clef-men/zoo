(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

type 'a t =
  { deques: 'a Ws_deques_public.t;
    rounds: Random_round.t array;
    waiters: Waiters.t;
    mutable killed: bool;
  }

let create sz =
  { deques= Ws_deques_public.create sz;
    rounds= Array.unsafe_init sz (fun _ -> Random_round.create @@ Int.positive_part @@ sz - 1);
    waiters= Waiters.create ();
    killed= false;
  }

let size t =
  Array.size t.rounds

let block t i =
  Ws_deques_public.block t.deques i

let unblock t i =
  Ws_deques_public.unblock t.deques i

let killed t =
  t.killed

let notify t =
  Waiters.notify t.waiters
let notify_all t =
  Waiters.notify_many t.waiters (size t)

let push t i v =
  Ws_deques_public.push t.deques i v ;
  notify t

let pop t i =
  Ws_deques_public.pop t.deques i

let try_steal_once t i =
  let round = Array.unsafe_get t.rounds i in
  Random_round.reset round ;
  Ws_deques_public.steal_as t.deques i round

let rec try_steal t i yield max_round until =
  if max_round <= 0 then
    Optional.Nothing
  else
    match try_steal_once t i with
    | Some v ->
        Optional.Something v
    | None ->
        if until () then
          Optional.Anything
        else (
          if yield then
            Domain.yield () ;
          try_steal t i yield (max_round - 1) until
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
let steal_until t i max_round_noyield pred =
  match try_steal t i false max_round_noyield pred with
  | Optional.Something v ->
      Some v
  | Anything ->
      None
  | Nothing ->
      steal_until t i pred
let steal_until t i max_round_noyield pred =
  block t i ;
  let res = steal_until t i max_round_noyield pred in
  unblock t i ;
  res

let steal_aux t i max_round_noyield max_round_yield until =
  match try_steal t i false max_round_noyield until with
  | Optional.Something _ as res ->
      res
  | Anything ->
      Anything
  | Nothing ->
      try_steal t i true max_round_yield until
let rec steal t i max_round_noyield max_round_yield =
  match steal_aux t i max_round_noyield max_round_yield (fun () -> killed t) with
  | Optional.Something v ->
      Some v
  | Anything ->
      None
  | Nothing ->
      let waiters = t.waiters in
      let waiter = Waiters.prepare_wait waiters in
      match try_steal_once t i with
      | Some _ as res ->
          Waiters.cancel_wait waiters waiter ;
          res
      | None ->
          if killed t then (
            Waiters.cancel_wait waiters waiter ;
            None
          ) else (
            Waiters.commit_wait waiters waiter ;
            steal t i max_round_noyield max_round_yield
          )
let steal t i max_round_noyield pred =
  block t i ;
  let res = steal t i max_round_noyield pred in
  unblock t i ;
  res

let kill t =
  t.killed <- true ;
  notify_all t

let pop_steal_until t i max_round_noyield pred =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal_until t i max_round_noyield pred

let pop_steal t i max_round_noyield max_round_yield =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal t i max_round_noyield max_round_yield
