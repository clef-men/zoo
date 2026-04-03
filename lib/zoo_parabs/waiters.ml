type t = Waiter.t Mpmc_queue_1.t

let create () = Mpmc_queue_1.create ()

let push waiters waiter =
  Mpmc_queue_1.push waiters waiter

let rec notify_one waiters =
  match Mpmc_queue_1.pop waiters with
  | None -> ()
  | Some waiter ->
    match Waiter.notify waiter with
    | First -> ()
    | Already_notified ->
      notify_one waiters

let rec notify_all waiters =
  match Mpmc_queue_1.pop waiters with
  | None -> ()
  | Some waiter ->
    ignore (Waiter.notify waiter);
    notify_all waiters
