type t =
  { mutable flag: bool;
    mutex: Mutex.t;
    condition: Condition.t;
  }

let create () =
  { flag= false;
    mutex= Mutex.create ();
    condition= Condition.create ();
  }

let notify t =
  if t.flag then
    true
  else
    let res =
      Mutex.protect t.mutex (fun () ->
        if t.flag then (
          true
        ) else (
          t.flag <- true ;
          false
        )
      )
    in
    Condition.notify t.condition ;
    res

let try_wait t =
  t.flag

let wait t =
  if not @@ try_wait t then
    let mtx = t.mutex in
    let cond = t.condition in
    Mutex.protect mtx (fun () ->
      Condition.wait_until cond mtx (fun () -> t.flag)
    )
