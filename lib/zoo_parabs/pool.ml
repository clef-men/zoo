type context =
  { context_hub: job Ws_hub_std.t;
    context_id: int;
  }

and job =
  context -> unit

type t =
  { hub: job Ws_hub_std.t;
    domains: unit Domain.t array;
  }

type 'a task =
  context -> 'a

type 'a future =
  'a Spmc_future.t

let[@zoo.opaque] max_round_noyield =
  1024
let[@zoo.opaque] max_round_yield =
  32

let execute ctx job =
  job ctx

let rec worker ctx =
  match Ws_hub_std.pop_steal ctx.context_hub ctx.context_id max_round_noyield max_round_yield with
  | None ->
      ()
  | Some job ->
      execute ctx job ;
      worker ctx

let create sz =
  let hub = Ws_hub_std.create (sz + 1) in
  let domains =
    Array.unsafe_initi sz (fun i ->
      Domain.spawn (fun () -> worker { context_hub= hub; context_id= i + 1 })
    )
  in
  { hub; domains }

let run t job =
  execute { context_hub= t.hub; context_id= 0 } job

let silent_async ctx task =
  Ws_hub_std.push ctx.context_hub ctx.context_id task
let async ctx task =
  let fut = Spmc_future.create () in
  silent_async ctx (fun ctx ->
    Spmc_future.set fut (task ctx)
  ) ;
  fut

let rec wait_until ctx pred =
  if not @@ pred () then
    match Ws_hub_std.pop_steal_until ctx.context_hub ctx.context_id max_round_noyield pred with
    | None ->
        ()
    | Some job ->
        execute ctx job ;
        wait_until ctx pred
let wait_while ctx pred =
  wait_until ctx (fun () -> not @@ pred ())

let await ctx fut =
  wait_until ctx (fun () -> Spmc_future.is_set fut) ;
  Spmc_future.get fut

let kill t =
  Ws_hub_std.kill t.hub ;
  Array.iter Domain.join t.domains
