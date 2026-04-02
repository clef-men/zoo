type 'a t =
  { size: int
  ; queue: 'a Mpmc_queue_1.t
  ; sleepers: Sleeper.t array
  ; dormitory: Dormitory.t
  ; mutable killed: bool
  }

let create sz =
  { size= sz
  ; queue= Mpmc_queue_1.create ()
  ; sleepers= Array.unsafe_initi sz Sleeper.create
  ; dormitory= Dormitory.create ()
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
  Dormitory.wakeup_one t.dormitory

let pop' t =
  Mpmc_queue_1.pop t.queue
let pop t _i =
  pop' t

let rec steal_aux t i ~finished ~prepare_sleep =
  let sleeper = t.sleepers.(i) in
  Sleeper.prepare_sleep sleeper;
  Dormitory.push t.dormitory sleeper;
  prepare_sleep (fun () -> ignore (Sleeper.wakeup sleeper));
  if finished () then (
    begin match Sleeper.cancel_sleep sleeper with
      | Wakeup_received -> Dormitory.wakeup_one t.dormitory
      | No_wakeup -> ()
    end;
    None
  ) else (
    match pop t i with
    | Some _ as res ->
        (* We are stealing a task that woke someone up,
           so they will have a spurious wakeup. *)
        ignore (Sleeper.cancel_sleep sleeper);
        res
    | None ->
        Sleeper.commit_sleep sleeper;
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
