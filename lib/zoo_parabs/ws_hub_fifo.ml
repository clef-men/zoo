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
  Waiters.notify_one t.waiters
let notify_all t =
  Waiters.notify_all t.waiters

let push t _i v =
  Mpmc_queue_1.push t.queue v ;
  notify t

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

let rec steal_aux t i ~notification ~pred =
  Waiters.prepare_wait t.waiters i ;
  notification (fun () -> Waiters.notify t.waiters i) ;
  if pred () then (
    if not @@ Waiters.cancel_wait t.waiters i then
      Waiters.notify_one t.waiters ;
    None
  ) else (
    match pop' t with
    | Some _ as res ->
        Waiters.cancel_wait t.waiters i |> ignore ;
        res
    | None ->
        Waiters.commit_wait t.waiters i ;
        steal_aux t i ~notification:ignore ~pred
  )

let steal_until t i ~max_round_noyield:_ ~max_round_yield:_ ~notification ~pred =
  steal_aux t i ~notification ~pred

let steal t i ~max_round_noyield:_ ~max_round_yield:_ =
  begin_inactive t ;
  let res =
    steal_aux
      t
      i
      ~notification:ignore
      ~pred:(fun () -> closed t)
  in
  begin match res with
  | None ->
      notify_all t
  | Some _ ->
      end_inactive t
  end ;
  res

let close =
  begin_inactive

let pop_steal_until t i ~max_round_noyield ~max_round_yield ~notification ~pred =
  if pred () then
    None
  else
    match pop t i with
    | Some _ as res ->
        res
    | None ->
        steal_until t i ~max_round_noyield ~max_round_yield ~notification ~pred

let pop_steal t i ~max_round_noyield ~max_round_yield =
  match pop t i with
  | Some _ as res ->
      res
  | None ->
      steal t i ~max_round_noyield ~max_round_yield
