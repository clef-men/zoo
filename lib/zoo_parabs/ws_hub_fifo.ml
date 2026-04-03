type 'a t =
  { size: int
  ; queue: 'a Mpmc_queue_1.t
  ; all_waiters: Waiter.t array
  ; waiters: Waiters.t
  ; mutable killed: bool
  }

let create sz =
  { size= sz
  ; queue= Mpmc_queue_1.create ()
  ; all_waiters= Array.unsafe_init sz Waiter.create
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

let push t _i v =
  Mpmc_queue_1.push t.queue v ;
  Waiters.notify_one t.waiters

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

let rec steal_aux t i ~finished ~prepare_sleep =
  let waiter = t.all_waiters.(i) in
  Waiter.prepare waiter;
  Waiters.push t.waiters waiter;
  prepare_sleep (fun () -> ignore (Waiter.notify waiter));
  if finished () then (
    begin match Waiter.cancel waiter with
      | Already_notified -> Waiters.notify_one t.waiters
      | First -> ()
    end;
    None
  ) else (
    match pop t i with
    | Some _ as res ->
        (* We are stealing a task that woke someone up,
           so they will have a spurious notify. *)
        ignore (Waiter.cancel waiter);
        res
    | None ->
        Waiter.commit waiter;
        steal_aux t i ~finished ~prepare_sleep
  )

let steal_until t i _max_round_noyield _max_round_yield ~finished ~prepare_sleep =
  steal_aux t i ~finished ~prepare_sleep

let steal t i _max_round_noyield _max_round_yield =
  steal_aux t i
    ~finished:(fun () -> killed t)
    ~prepare_sleep:ignore

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
