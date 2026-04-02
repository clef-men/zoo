type t = Sleeper.t Mpmc_queue_1.t

let create () = Mpmc_queue_1.create ()

let push dorm sleeper =
  Mpmc_queue_1.push dorm sleeper

let rec wakeup_one dorm =
  match Mpmc_queue_1.pop dorm with
  | None -> ()
  | Some sleeper ->
    if not (Sleeper.wakeup sleeper)
    then wakeup_one dorm

let rec wakeup_all dorm =
  match Mpmc_queue_1.pop dorm with
  | None -> ()
  | Some sleeper ->
    ignore (Sleeper.wakeup sleeper);
    wakeup_all dorm
