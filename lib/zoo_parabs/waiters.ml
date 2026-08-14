type t =
  { waiters: Waiter.t array
  ; queue: Waiter.t Queue_mpmc_1.t
  }

let create sz =
  { waiters= Array.unsafe_init sz Waiter.create
  ; queue= Queue_mpmc_1.create ()
  }

let notify t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.notify waiter |> ignore

let rec notify_one t =
  match Queue_mpmc_1.pop t.queue with
  | None ->
      ()
  | Some waiter ->
      if not @@ Waiter.notify waiter then
        notify_one t

let rec notify_all t =
  match Queue_mpmc_1.pop t.queue with
  | None ->
      ()
  | Some waiter ->
      Waiter.notify waiter |> ignore ;
      notify_all t

let prepare_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.prepare_wait waiter ;
  Queue_mpmc_1.push t.queue waiter

let cancel_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.cancel_wait waiter

let commit_wait t i =
  let waiter = Array.unsafe_get t.waiters i in
  Waiter.commit_wait waiter
