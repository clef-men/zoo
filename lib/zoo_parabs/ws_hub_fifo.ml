type 'a t =
  { size: int
  ; queue: 'a Mpmc_queue_1.t
  ; waiters: Waiters.t
  ; mutable killed: bool
  }

let create sz =
  { size= sz
  ; queue= Mpmc_queue_1.create ()
  ; waiters= Waiters.create ()
  ; killed= false
  }

let size t =
  t.size

let block _t _i =
  ()

let unblock _t _i =
  ()

let killed t =
  t.killed

let notify t =
  Waiters.notify t.waiters (size t)
let notify_all t =
  Waiters.notify_all t.waiters

let push t _i v =
  Mpmc_queue_1.push t.queue v ;
  notify t

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

let rec steal_until_aux t max_round trigger =
  match pop' t with
  | Some _ as res ->
      res
  | None ->
      if Trigger.probe trigger then
        None
      else (
        Domain.yield () ;
        steal_until_aux t (max_round - 1) trigger
      )
let rec steal_until t max_round trigger =
  match steal_until_aux t max_round trigger with
  | Some _ as res ->
      res
  | None ->
      Waiters.push t.waiters trigger ;
      if Trigger.wait trigger then
        None
      else
        steal_until t max_round trigger
let steal_until t _i _max_round_noyield max_round_yield trigger =
  steal_until t max_round_yield trigger

let rec steal t =
  let waiters = t.waiters in
  let trigger = Waiters.prepare_wait waiters in
  if killed t then (
    Waiters.cancel_wait waiters trigger (size t) ;
    None
  ) else (
    if Mpmc_queue_1.is_empty t.queue then (
      Waiters.commit_wait waiters trigger
    ) else (
      Waiters.cancel_wait waiters trigger (size t)
    ) ;
    match pop' t with
    | Some _ as res ->
        res
    | None ->
        steal t
  )
let steal t _i _max_round_noyield _max_round_yield =
  steal t

let kill t =
  t.killed <- true ;
  notify_all t

let pop_steal_until t i max_round_noyield max_round_yield trigger =
  if Trigger.probe trigger then
    None
  else
    match pop t i with
    | Some _ as res ->
        res
    | None ->
        steal_until t i max_round_noyield max_round_yield trigger

let pop_steal t i max_round_noyield max_round_yield =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal t i max_round_noyield max_round_yield
