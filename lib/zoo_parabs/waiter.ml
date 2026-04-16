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
  if t.flag then (
    false
  ) else (
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
  )

let prepare_wait t =
  t.flag <- false

let cancel_wait t =
  t.flag <- true

let commit_wait t =
  if not @@ t.flag then
    Mutex.protect t.mutex @@ fun () ->
      Condition.wait_until t.condition t.mutex (fun () -> t.flag)
