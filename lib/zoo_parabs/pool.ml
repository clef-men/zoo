type context =
  { context_size: int
  ; context_hub: job Ws_hub_std.t
  ; context_id: int
  }

and job =
  context -> unit

type t =
  { size: int
  ; hub: job Ws_hub_std.t
  ; domains: unit Domain.t array
  ; mutable force_mutable: unit (* for verification *)
  }

type 'a task =
  context -> 'a

let max_round_noyield =
  1024
let max_round_yield =
  32

let context sz hub id =
  { context_size= sz
  ; context_hub= hub
  ; context_id= id
  }
let context_main t =
  context t.size t.hub 0

let execute ctx job =
  job ctx

let rec worker ctx =
  match
    Ws_hub_std.pop_steal
      ctx.context_hub
      ctx.context_id
      ~max_round_noyield
      ~max_round_yield
  with
  | None ->
      ()
  | Some job ->
      execute ctx job ;
      worker ctx

let create ~num_worker:sz =
  let hub = Ws_hub_std.create (sz + 1) in
  Ws_hub_std.block hub 0 ;
  let domains =
    Array.unsafe_initi sz (fun i ->
      Domain.spawn (fun () -> worker @@ context sz hub (i + 1))
    )
  in
  { size= sz
  ; hub
  ; domains
  ; force_mutable= ()
  }

let run_on t task =
  Ws_hub_std.unblock t.hub 0 ;
  let res = execute (context_main t) task in
  Ws_hub_std.block t.hub 0 ;
  res

let close t =
  Ws_hub_std.close t.hub ;
  Ws_hub_std.unblock t.hub 0 ;
  worker (context_main t) ;
  Array.iter Domain.join t.domains

let run ~num_worker task =
  let t = create ~num_worker in
  let res = run_on t task in
  close t ;
  res

let size ctx =
  ctx.context_size

let async ctx task =
  Ws_hub_std.push ctx.context_hub ctx.context_id task

let rec wait ctx ~notification ~pred =
  match
    Ws_hub_std.pop_steal_until
      ctx.context_hub
      ctx.context_id
      ~max_round_noyield
      ~max_round_yield
      ~notification
      ~pred
  with
  | None ->
      ()
  | Some job ->
      execute ctx job ;
      wait ctx ~notification ~pred
let wait ctx ~notification ~pred =
  let notification_registered = ref false in
  let notification notify =
    if not !notification_registered then (
      notification_registered := true ;
      notification notify
    )
  in
  wait ctx ~notification ~pred

let wait_ivar ctx ivar =
  wait
    ctx
    ~notification:(fun notify ->
      Ivar_3.wait ivar (fun _ctx _v -> notify ()) |> ignore
    )
    ~pred:(fun () ->
      Ivar_3.is_set ivar
    )
