type 'a t =
  ('a, ('a -> unit) Pool.task) Ivar_3.t

let[@inline] set ctx t res =
  let waiters = Ivar_3.set t res in
  Lst.iter (fun waiter -> waiter ctx res) waiters

let async ctx task =
  let t = Ivar_3.create () in
  Pool.async ctx (fun ctx -> set ctx t (task ctx)) ;
  t

let wait ctx t =
  Pool.wait_until ctx (fun () -> Ivar_3.is_set t) ;
  Ivar_3.get t

let iter ctx t task =
  match Ivar_3.wait t task with
  | None ->
      ()
  | Some res ->
      task ctx res

let map ctx t1 task =
  let t2 = Ivar_3.create () in
  iter ctx t1 (fun ctx res1 ->
    Pool.async ctx @@ fun ctx ->
      set ctx t2 (task ctx res1)
  ) ;
  t2
