type 'a t =
  (Pool.context, 'a) Ivar_4.t

let return =
  Ivar_4.make

let[@inline] set ctx t res =
  Ivar_4.notify t ctx res

let async ctx task =
  let t = Ivar_4.create () in
  Pool.async ctx (fun ctx -> set ctx t (task ctx)) ;
  t

let wait ctx t =
  Pool.wait_ivar ctx t ;
  Ivar_4.get t

let iter ctx t task =
  match Ivar_4.wait t task with
  | None ->
      ()
  | Some res ->
      task ctx res

let map ctx t1 task =
  let t2 = Ivar_4.create () in
  iter ctx t1 (fun ctx res1 ->
    Pool.async ctx @@ fun ctx ->
      set ctx t2 (task ctx res1)
  ) ;
  t2
