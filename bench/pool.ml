module type S =
  Pool_intf.S

module Parabs : S =
  Zoo_parabs.Pool

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

  let create num_domains =
    Task.setup_pool ~num_domains ()

  let run t task =
    Task.run t (fun () -> task t)

  let kill =
    Task.teardown_pool

  let async t task =
    Task.async t (fun () -> task t)

  let wait =
    Task.await
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

  let create num_threads =
    Fifo_pool.create ~num_threads ()

  let run t task =
    Fifo_pool.run_wait_block t (fun () -> task t)

  let kill =
    Fifo_pool.shutdown

  let async t task =
    Fut.spawn ~on:t (fun () -> task t)

  let wait _t fut =
    Fut.await fut
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

  let create num_threads =
    Ws_pool.create ~num_threads ()

  let run t task =
    Ws_pool.run_wait_block t (fun () -> task t)

  let kill =
    Ws_pool.shutdown

  let async t task =
    Fut.spawn ~on:t (fun () -> task t)

  let wait _t fut =
    Fut.await fut
end
