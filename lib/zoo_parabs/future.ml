type 'a t =
  ('a, ('a -> unit) Pool.task) Ivar_3.t

let return =
  Ivar_3.make

let[@inline] set ctx t res =
  let waiters = Ivar_3.set t res in
  Lst.iter (fun waiter -> waiter ctx res) waiters

let async ctx task =
  let t = Ivar_3.create () in
  Pool.async ctx (fun ctx -> set ctx t (task ctx)) ;
  t

let wait ctx t =
  if Ivar_3.is_set t then (
    ()
  ) else (
    let trigger = Trigger.create (fun () -> Ivar_3.is_set t) in
    match Ivar_3.wait t (fun _ctx _ -> Trigger.notify trigger) with
    | Some _ ->
        ()
    | None ->
        Pool.wait ctx trigger
  ) ;
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
