module type S =
  Pool_intf.S

module Parabs : S = struct
  open Zoo_parabs

  type t =
    Pool.t

  type context =
    Pool.context

  type 'a task =
    context -> 'a

  type 'a future =
    'a Pool.future

  let create ~num_domains () =
    Pool.create num_domains

  let run =
    Pool.run

  let kill =
    Pool.kill

  let async =
    Pool.async

  let wait =
    Pool.wait

  let for_ ctx ~beg ~end_ ~chunk fn =
    Algo.for_ ctx beg end_ chunk fn

  let divide ctx ~beg ~end_ fn =
    Algo.divide ctx beg end_ fn
end

module Domainslib : S = struct
  open Domainslib

  type t =
    Task.pool

  type context =
    t

  type 'a task =
    context -> 'a

  type 'a future =
    'a Task.promise

  let create ~num_domains () =
    Task.setup_pool ~num_domains ()

  let run t task =
    Task.run t (fun () -> task t)

  let kill =
    Task.teardown_pool

  let async t task =
    Task.async t (fun () -> task t)

  let wait =
    Task.await

  let for_ t ~beg ~end_ ~chunk fn =
    Task.parallel_for t ~chunk_size:chunk ~start:beg ~finish:(end_ - 1) ~body:(fn t)

  let divide t ~beg ~end_ fn =
    let num_dom = Task.get_num_domains t in
    let sz = end_ - beg in
    let chunk = sz / num_dom in
    let rest = sz mod num_dom in
    let num_chunk = num_dom + Bool.to_int (rest != 0) in
    let futs =
      Array.init num_chunk @@ fun i ->
        Task.async t @@ fun () ->
          fn t (i * chunk) (if i == num_dom then rest else chunk)
    in
    Array.iter (Task.await t) futs
end

module Moonpool_fifo : S = struct
  open Moonpool

  type t =
    Fifo_pool.t

  type context =
    t

  type 'a task =
    context -> 'a

  type 'a future =
    'a Fut.t

  let create ~num_domains () =
    Fifo_pool.create ~num_threads:num_domains ()

  let run t task =
    Fifo_pool.run_wait_block t (fun () -> task t)

  let kill =
    Fifo_pool.shutdown

  let async t task =
    Fut.spawn ~on:t (fun () -> task t)

  let wait _t fut =
    Fut.await fut

  let for_ t ~beg ~end_ ~chunk fn =
    Moonpool_forkjoin.for_ (end_ - beg) ~chunk_size:chunk @@ fun beg' end' ->
      for i = beg + beg' to beg + end' do
        fn t i
      done

  let divide t ~beg ~end_ fn =
    Moonpool_forkjoin.for_ (end_ - beg) @@ fun beg' end' ->
      fn t (beg + beg') (end' - beg')
end

module Moonpool_ws : S = struct
  open Moonpool

  type t =
    Ws_pool.t

  type context =
    t

  type 'a task =
    context -> 'a

  type 'a future =
    'a Fut.t

  let create ~num_domains () =
    Fifo_pool.create ~num_threads:num_domains ()

  let run t task =
    Ws_pool.run_wait_block t (fun () -> task t)

  let kill =
    Ws_pool.shutdown

  let async t task =
    Fut.spawn ~on:t (fun () -> task t)

  let wait _t fut =
    Fut.await fut

  let for_ t ~beg ~end_ ~chunk fn =
    Moonpool_forkjoin.for_ (end_ - beg) ~chunk_size:chunk @@ fun beg' end' ->
      for i = beg + beg' to beg + end' do
        fn t i
      done

  let divide t ~beg ~end_ fn =
    Moonpool_forkjoin.for_ (end_ - beg) @@ fun beg' end' ->
      fn t (beg + beg') (end' - beg')
end
