type 'a t =
  ('a, ('a -> unit) Pool.task) Ivar_3.t

let async ctx task =
  let t = Ivar_3.create () in
  Pool.async ctx (fun ctx ->
    let res = task ctx in
    let waiters = Ivar_3.set t res in
    Lst.iter (fun waiter -> waiter ctx res) waiters
  ) ;
  t

let wait ctx t =
  Pool.wait_until ctx (fun () -> Ivar_3.is_set t) ;
  Ivar_3.get t

let iter ctx t fn =
  match Ivar_3.wait t fn with
  | None ->
      ()
  | Some res ->
      fn ctx res

let map ctx t1 fn =
  let t2 = Ivar_3.create () in
  iter ctx t1 (fun ctx res1 ->
    let res2 = fn ctx res1 in
    let waiters = Ivar_3.set t2 res2 in
    Lst.iter (fun waiter -> waiter ctx res2) waiters
  ) ;
  t2
