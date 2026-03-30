(* Based on:
   https://github.com/ocaml-multicore/domainslib/blob/731f08891c87e788f2cc95f2a600328f6682a5e2/lib/multi_channel.ml
*)

type 'a t =
  { queues: 'a Ws_deques_public.t
  ; rounds: Random_round.t array
  ; sleepers: Sleeper.t array
  ; dormitory: Dormitory.t
  ; mutable killed: bool [@atomic]
  }

let create sz =
  { queues= Ws_deques_public.create sz
  ; rounds= Array.unsafe_init sz (fun _ -> Random_round.create @@ Int.positive_part @@ sz - 1)
  ; sleepers= Array.unsafe_initi sz Sleeper.create
  ; dormitory= Dormitory.create ()
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
  Dormitory.wakeup_one t.dormitory

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
      let sleeper = t.sleepers.(i) in
      Sleeper.prepare_sleep sleeper;
      Dormitory.push t.dormitory sleeper;
      match try_steal_once t i with
      | Some _ as res ->
        (* We are stealing a task that woke someone up,
           so they will have a spurious wakeup. *)
        ignore (Sleeper.cancel_sleep sleeper);
        res
      | None ->
        if not (prepare_sleep (fun () -> ignore (Sleeper.wakeup sleeper))) then (
          if not (Sleeper.cancel_sleep sleeper) then
            Dormitory.wakeup_one t.dormitory;
          None
        ) else (
          Sleeper.commit_sleep sleeper;
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
      ~finished:(fun () -> killed t) ~prepare_sleep:(fun _ -> not (killed t))
  in
  unblock t i ;
  res

let kill t =
  t.killed <- true ;
  Dormitory.wakeup_all t.dormitory

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
