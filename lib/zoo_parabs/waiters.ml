type t =
  { waiters: Waiter.t array
  ; queue: Waiter.t Mpmc_queue_1.t
  }

let create sz =
  { waiters= Array.unsafe_init sz Waiter.create
  ; queue= Mpmc_queue_1.create ()
  }

let rec notify t =
  match Mpmc_queue_1.pop t.queue with
  | None ->
      ()
  | Some waiter ->
      if not @@ Waiter.notify waiter then
        notify t

let rec notify_all t =
  match Mpmc_queue_1.pop t.queue with
  | None ->
      ()
  | Some waiter ->
      Waiter.notify waiter |> ignore ;
      notify_all t

let prepare_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.prepare_wait waiter ;
  Mpmc_queue_1.push t.queue waiter

let cancel_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.cancel_wait waiter

let commit_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.commit_wait waiter
