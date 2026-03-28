type t =
  { mutex: Mutex.t;
    condition: Condition.t;
    mutable flag: bool;
  }

let create () =
  { mutex= Mutex.create ();
    condition= Condition.create ();
    flag= false;
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
    Mutex.protect mtx @@ fun () ->
      Condition.wait_until cond mtx (fun () -> t.flag)
