type 'a t =
  { size: int;
    queue: 'a Mpmc_queue_1.t;
    waiters: Waiters.t;
    mutable killed: bool;
  }

let create sz =
  { size= sz;
    queue= Mpmc_queue_1.create ();
    waiters= Waiters.create ();
    killed= false;
  }

let size t =
  t.size

let notify t =
  Waiters.notify t.waiters
let notify_all t =
  Waiters.notify_many t.waiters (size t)

let push t _i v =
  Mpmc_queue_1.push t.queue v ;
  notify t

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

let killed t =
  t.killed

let rec steal_until t pred =
  if pred () then (
    None
  ) else (
    Domain.yield () ;
    match pop' t with
    | Some _ as res ->
        res
    | None ->
        steal_until t pred
  )
let steal_until t _i _max_round_noyield pred =
  steal_until t pred

let rec steal t =
  let waiters = t.waiters in
  let waiter = Waiters.prepare_wait waiters in
  if killed t then (
    Waiters.cancel_wait waiters waiter ;
    None
  ) else (
    if Mpmc_queue_1.is_empty t.queue then (
      Waiters.commit_wait waiters waiter
    ) else (
      Waiters.cancel_wait waiters waiter
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
