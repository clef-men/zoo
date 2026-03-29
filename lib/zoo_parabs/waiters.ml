type t =
  Trigger.t Mpmc_queue_1.t

let create =
  Mpmc_queue_1.create

let rec notify t max_attempt =
  if 0 < max_attempt then
    match Mpmc_queue_1.pop t with
    | None ->
        ()
    | Some trigger ->
        if Trigger.notify_weak trigger then
          ()
        else
          notify t (max_attempt - 1)

let rec notify_all t =
  match Mpmc_queue_1.pop t with
  | None ->
      ()
  | Some trigger ->
      Trigger.notify trigger ;
      notify_all t

let push =
  Mpmc_queue_1.push

let prepare_wait t =
  let trigger =
    let flag = ref false in
    Trigger.create @@ fun () ->
      if !flag then (
        true
      ) else (
        flag := true ;
        false
      )
  in
  push t trigger ;
  trigger

let cancel_wait t trigger max_notify_attempt =
  if Trigger.probe trigger then
    notify t max_notify_attempt

let commit_wait _t trigger =
  Trigger.wait trigger |> ignore
