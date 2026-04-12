type 'a t =
  { size: int
  ; queue: 'a Mpmc_queue_1.t
  ; waiters: Waiters.t
  ; mutable num_active: int [@atomic]
  }

let create sz =
  { size= sz
  ; queue= Mpmc_queue_1.create ()
  ; waiters= Waiters.create sz
  ; num_active= sz + 1
  }

let size t =
  t.size

let begin_inactive t =
  Atomic.Loc.decr [%atomic.loc t.num_active]
let end_inactive t =
  Atomic.Loc.incr [%atomic.loc t.num_active]

let block t _i =
  begin_inactive t
let unblock t _i =
  end_inactive t

let closed t =
  t.num_active == 0

let notify t =
  Waiters.notify t.waiters
let notify_all t =
  Waiters.notify_all t.waiters

let push t _i v =
  Mpmc_queue_1.push t.queue v ;
  notify t

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

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
let steal_until t _i ~max_round_noyield:_ pred =
  steal_until t pred

let rec steal t i =
  Waiters.prepare_wait t.waiters i ;
  if closed t then (
    notify_all t ;
    None
  ) else (
    if Mpmc_queue_1.is_empty t.queue then (
      Waiters.commit_wait t.waiters i
    ) else (
      Waiters.cancel_wait t.waiters i
    ) ;
    match pop' t with
    | Some _ as res ->
        end_inactive t ;
        res
    | None ->
        steal t i
  )
let steal t i ~max_round_noyield:_ ~max_round_yield:_ =
  begin_inactive t ;
  steal t i

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
