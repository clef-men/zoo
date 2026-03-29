type t =
  { mutex: Mutex.t
  ; condition: Condition.t
  ; predicate: unit -> bool
  }

let create pred =
  { mutex= Mutex.create ()
  ; condition= Condition.create ()
  ; predicate= pred
  }

let[@inline] probe t =
  t.predicate ()

let notify_weak t =
  if probe t then (
    false
  ) else (
    Condition.notify t.condition ;
    true
  )

let notify t =
  Mutex.protect t.mutex @@ fun () ->
    Condition.notify t.condition

let wait t =
  Mutex.protect t.mutex @@ fun () ->
    if probe t then (
      true
    ) else (
      Condition.wait t.condition t.mutex ;
      false
    )
