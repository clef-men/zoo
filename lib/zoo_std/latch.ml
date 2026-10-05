type t =
  { mutable counter: int
  ; mutex: Mutex.t
  ; condition: Condition.t
  }

let create sz =
  { counter= sz
  ; mutex= Mutex.create ()
  ; condition= Condition.create ()
  }

let wait t =
  Mutex.protect t.mutex @@ fun () ->
    t.counter <- t.counter - 1 ;
    Condition.wait_until t.condition t.mutex @@ fun () ->
      t.counter == 0
