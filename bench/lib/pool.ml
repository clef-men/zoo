module _ (* Moonpool_forkjoin *) = struct
  [@@@warning "-a"]
  open Moonpool

  let for_ ?chunk_size n f =
    if n > 0 then
      let runner =
        match Runner.get_current_runner () with
        | None ->
            failwith "forkjoin.for_: must be run inside a moonpool runner."
        | Some r ->
            r
      in

      let missing = Atomic.make n in

      let chunk_size =
        match chunk_size with
        | Some cs -> max 1 (min n cs)
        | None ->
          (* guess: try to have roughly one task per core *)
          max 1 (1 + (n / Private.num_domains ()))
      in

      let fut, promise = Fut.make () in

      let task_for ~offset ~len_range =
        match f offset (offset + len_range - 1) with
        | () ->
          if Atomic.fetch_and_add missing (-len_range) = len_range then
            Fut.fulfill promise (Ok ())
        | exception exn ->
          let bt = Printexc.get_raw_backtrace () in
          Fut.fulfill_idempotent promise (Error (Exn_bt.make exn bt))
      in

      let i = ref 0 in
      while !i < n do
        let offset = !i in

        let len_range = min chunk_size (n - offset) in
        assert (offset + len_range <= n);

        Runner.run_async runner (fun () -> task_for ~offset ~len_range);
        i := !i + len_range
      done;

      Fut.wait_block_exn fut
end

include Pool_intf

module Make
  (Base : BASE)
= struct
  include Base

  let for_ ctx ~beg ~end_ ?chunk fn =
    let chunk =
      match chunk with
      | Some chunk ->
          chunk
      | None ->
          let num_dom = Base.size ctx + 1 in
          max 1 ((end_ - beg) / num_dom)
    in
    Base.for_ ctx ~beg ~end_ ~chunk fn
end

module Sequential = Make(struct
  type context = unit
  type 'a task = context -> 'a

  let size () = 1

  type t = unit

  let create ~num_domains:_ () = ()

  let run () task = task ()

  let kill () = ()

  type 'a future = unit -> 'a

  let async () task = task

  let wait () fut = fut ()

  let for_ () ~beg ~end_ ~chunk:_ f =
    for i = beg to end_ - 1 do
      f () i
    done

  let divide () ~beg ~end_ f =
    f () beg (end_ - beg)
end)

module Parabs = Make(struct
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

  let size =
    Pool.size

  let run =
    Pool.run

  let kill =
    Pool.kill

  let async =
    Pool.async

  let wait =
    Pool.wait

  let for_ ctx ~beg ~end_ ~chunk fn =
    Algo.for_2 ctx beg end_ chunk fn

  let divide ctx ~beg ~end_ fn =
    Algo.divide ctx beg end_ fn
end)

module Domainslib = Make(struct
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

  let size t =
    Task.get_num_domains t - 1

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
end)

module Moonpool_fifo = Make(struct
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

  let size _t =
    Moonpool.Private.num_domains ()

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
end)

module Moonpool_ws = Make(struct
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

  let size _t =
    Moonpool.Private.num_domains ()

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
end)

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
