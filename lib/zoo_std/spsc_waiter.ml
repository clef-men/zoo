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
  Mutex.protect t.mutex (fun () ->
    t.flag <- true
  ) ;
  Condition.notify t.condition

let try_wait t =
  t.flag

let wait t =
  if not @@ try_wait t then
    let mtx = t.mutex in
    let cond = t.condition in
    Mutex.protect mtx (fun () ->
      Condition.wait_until cond mtx (fun () -> t.flag)
    )
