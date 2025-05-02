type context =
  { context_size: int;
    context_hub: job Ws_hub_std.t;
    context_id: int;
  }

and job =
  context -> unit

type t =
  { size: int;
    hub: job Ws_hub_std.t;
    domains: unit Domain.t array;
  }

type 'a task =
  context -> 'a

type 'a future =
  'a Ivar_3.t

let max_round_noyield =
  1024
let max_round_yield =
  32

let context sz hub id =
  { context_size= sz;
    context_hub= hub;
    context_id= id;
  }

let execute ctx job =
  job ctx

let rec worker ctx =
  match Ws_hub_std.pop_steal ctx.context_hub ctx.context_id max_round_noyield max_round_yield with
  | None ->
      Ws_hub_std.block ctx.context_hub ctx.context_id
  | Some job ->
      execute ctx job ;
      worker ctx

let create sz =
  let hub = Ws_hub_std.create (sz + 1) in
  Ws_hub_std.block hub 0 ;
  let domains =
    Array.unsafe_initi sz (fun i ->
      Domain.spawn (fun () -> worker @@ context sz hub (i + 1))
    )
  in
  { size= sz; hub; domains }

let run t job =
  Ws_hub_std.unblock t.hub 0 ;
  let res = execute (context t.size t.hub 0) job in
  Ws_hub_std.block t.hub 0 ;
  res

let kill t =
  Ws_hub_std.kill t.hub ;
  Array.iter Domain.join t.domains

let size ctx =
  ctx.context_size

let silent_async ctx task =
  Ws_hub_std.push ctx.context_hub ctx.context_id task
let async ctx task =
  let fut = Ivar_3.create () in
  silent_async ctx (fun ctx ->
    Ivar_3.set fut (task ctx) |> ignore
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
  wait_until ctx (fun () -> Ivar_3.is_set fut) ;
  Ivar_3.get fut
