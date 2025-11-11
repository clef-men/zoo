include Pool_intf

module Make
  (Base : BASE)
= struct
  include Base

  let adjust_chunk ~beg ~end_ ~chunk ctx =
    match chunk with
    | Some chunk ->
        chunk
    | None ->
        let num_dom = Base.size ctx + 1 in
        let num_task = end_ - beg in
        if num_dom == 1 then
          num_task
        else
          Int.max 1 (num_task / (8 * num_dom))

  let rec for_ ~beg ~end_ ~chunk ctx task =
    let num_task = end_ - beg in
    if num_task <= chunk then
      task ctx beg num_task
    else
      let mid = beg + num_task / 2 in
      let left =
        Base.async ctx @@ fun ctx ->
          for_ ctx ~beg ~end_:mid ~chunk task
      in
      for_ ctx ~beg:mid ~end_ ~chunk task ;
      Base.wait ctx left
  let for_ ~beg ~end_ ?chunk ctx task =
    let chunk = adjust_chunk ctx ~beg ~end_ ~chunk in
    for_ ctx ~beg ~end_ ~chunk task

  let for_each ~beg ~end_ ?chunk ctx task =
    for_ ctx ~beg ~end_ ?chunk @@ fun ctx beg sz ->
      for i = beg to beg + sz - 1 do
        task ctx i
      done
end

module Sequential = Make(struct
  type t =
    unit

  type context =
    unit

  type 'a task =
    context -> 'a

  let size () =
    0

  let create ~num_domain:_ () =
    ()

  let run () task =
    task ()

  let kill () =
    ()

  type 'a future =
    unit -> 'a

  let async () task =
    task

  let wait () fut =
    fut ()
end)

module Parabs = Make(struct
  open Zoo_parabs

  type t =
    Pool.t

  type context =
    Pool.context

  type 'a task =
    context -> 'a

  let create ~num_domain () =
    Pool.create num_domain

  let size =
    Pool.size

  let run =
    Pool.run

  let kill =
    Pool.kill

  type 'a future =
    'a Future.t

  let async =
    Future.async

  let wait =
    Future.wait
end)

module Domainslib = Make(struct
  open Domainslib

  type t =
    Task.pool

  type context =
    t

  type 'a task =
    context -> 'a

  let create ~num_domain () =
    Task.setup_pool ~num_domains:num_domain ()

  let size t =
    Task.get_num_domains t - 1

  let run t task =
    Task.run t (fun () -> task t)

  let kill =
    Task.teardown_pool

  type 'a future =
    'a Task.promise

  let async t task =
    Task.async t (fun () -> task t)

  let wait =
    Task.await
end)

module Moonpool_fifo_base = struct
  open Moonpool

  type t =
    { size: int;
      pool: Fifo_pool.t;
    }

  type context =
    t

  type 'a task =
    context -> 'a

  let create ~num_domain () =
    (* ask for one more domain on Moonpool, see
       https://github.com/c-cube/moonpool/issues/41 *)
    let pool = Fifo_pool.create ~num_threads:(num_domain + 1) () in
    { size= num_domain; pool }

  let size t =
    t.size

  let run t task =
    Fifo_pool.run_wait_block t.pool (fun () -> task t)

  let kill t =
    Fifo_pool.shutdown t.pool

  type 'a future =
    'a Fut.t

  let async t task =
    Fut.spawn ~on:t.pool (fun () -> task t)

  let wait _t fut =
    Fut.await fut
end
module Moonpool_fifo =
  Make(Moonpool_fifo_base)

module Moonpool_ws_base = struct
  open Moonpool

  type t =
    { size: int;
      pool: Ws_pool.t;
    }

  type context =
    t

  type 'a task =
    context -> 'a

  let create ~num_domain () =
    (* ask for one more domain on Moonpool, see
       https://github.com/c-cube/moonpool/issues/41 *)
    let pool = Ws_pool.create ~num_threads:(num_domain + 1) () in
    { size= num_domain; pool }

  let size t =
    t.size

  let run t task =
    Ws_pool.run_wait_block t.pool (fun () -> task t)

  let kill t =
    Ws_pool.shutdown t.pool

  type 'a future =
    'a Fut.t

  let async t task =
    Fut.spawn ~on:t.pool (fun () -> task t)

  let wait _t fut =
    Fut.await fut
end
module Moonpool_ws =
  Make(Moonpool_ws_base)

let impl_of_string s : (module S) =
  match s with
  | "parabs" ->
      (module Parabs)
  | "domainslib" ->
      (module Domainslib)
  | "moonpool-fifo" ->
      (module Moonpool_fifo)
  | "moonpool-ws" ->
      (module Moonpool_ws)
  | "sequential" ->
      (module Sequential)
  | _ ->
      failwith "illegal method"
