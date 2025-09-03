type t =
  { mutex: Mutex.t;
    condition: Condition.t;
    mutable count: int;
  }

let create cap =
  { mutex= Mutex.create ();
    condition= Condition.create ();
    count= cap - 1;
  }

let try_lock t =
  Mutex.protect t.mutex @@ fun () ->
    let cnt = t.count in
    if 0 < cnt then (
      t.count <- cnt - 1 ;
      true
    ) else (
      false
    )

let lock t =
  Mutex.protect t.mutex @@ fun () ->
    Condition.wait_until t.condition t.mutex (fun () ->
      0 < t.count
    ) ;
    t.count <- t.count - 1

let unlock t =
  Mutex.protect t.mutex (fun () ->
    t.count <- t.count + 1
  ) ;
  Condition.notify t.condition
