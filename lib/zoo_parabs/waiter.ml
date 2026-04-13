type t =
  { mutex: Mutex.t
  ; condition: Condition.t
  ; mutable flag: bool
  }

let create () =
  { mutex= Mutex.create ()
  ; condition= Condition.create ()
  ; flag= false
  }

let notify t =
  Mutex.lock t.mutex ;
  if t.flag then (
    Mutex.unlock t.mutex ;
    false
  ) else (
    t.flag <- true ;
    Mutex.unlock t.mutex ;
    Condition.notify t.condition ;
    true
  )

let prepare_wait t =
  Mutex.protect t.mutex @@ fun () ->
    t.flag <- false

let cancel_wait t =
  Mutex.protect t.mutex @@ fun () ->
    t.flag <- true

let commit_wait t =
  Mutex.protect t.mutex @@ fun () ->
    Condition.wait_until t.condition t.mutex (fun () -> t.flag)
