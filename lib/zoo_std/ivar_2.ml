type 'a state =
  'a option

type 'a t =
  { mutable result: 'a state;
    mutex: Mutex.t;
    condition: Condition.t;
  }

let create () =
  { result= None;
    mutex= Mutex.create ();
    condition= Condition.create ();
  }

let make v =
  { result= Some v;
    mutex= Mutex.create ();
    condition= Condition.create ();
  }

let try_get t =
  t.result

let is_unset t =
  try_get t == None
let is_set t =
  not @@ is_unset t

let get t =
  match try_get t with
  | Some v ->
      Mutex.synchronize t.mutex ;
      v
  | None ->
      let mtx = t.mutex in
      let cond = t.condition in
      Mutex.protect mtx (fun () ->
        Condition.wait_while cond mtx (fun () ->
          t.result == None
        )
      ) ;
      match t.result with
      | Some v ->
          v
      | None ->
          assert false

let set t v =
  Mutex.protect t.mutex (fun () ->
    t.result <- Some v
  ) ;
  Condition.notify_all t.condition
