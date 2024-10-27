type 'a t =
  { mutable result: 'a option;
    mutex: Mutex.t;
    condition: Condition.t;
  }

let create () =
  { result= None;
    mutex= Mutex.create ();
    condition= Condition.create ();
  }

let set t v =
  Mutex.protect t.mutex (fun () ->
    t.result <- Some v
  ) ;
  Condition.notify_all t.condition

let try_get t =
  t.result

let get t =
  match try_get t with
  | Some v ->
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

let is_set t =
  match try_get t with
  | None ->
      false
  | Some _ ->
      true
