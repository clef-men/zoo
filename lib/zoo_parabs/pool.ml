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
  match Ws_hub_std.pop_steal ctx.context_hub ctx.context_id max_round_noyield max_round_yield with
  | None ->
      Ws_hub_std.block ctx.context_hub ctx.context_id
  | Some job ->
      execute ctx job ;
      worker ctx

let rec drain ctx =
  match Ws_hub_std.pop ctx.context_hub ctx.context_id with
  | None ->
      Ws_hub_std.block ctx.context_hub ctx.context_id
  | Some job ->
      execute ctx job ;
      drain ctx

let create sz =
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

let run t task =
  Ws_hub_std.unblock t.hub 0 ;
  let res = execute (context_main t) task in
  Ws_hub_std.block t.hub 0 ;
  res

let kill t =
  Ws_hub_std.unblock t.hub 0 ;
  drain (context_main t) ;
  Ws_hub_std.kill t.hub ;
  Array.iter Domain.join t.domains

let size ctx =
  ctx.context_size

let async ctx task =
  Ws_hub_std.push ctx.context_hub ctx.context_id task

let rec wait ctx ~finished ~prepare_sleep =
  match
    Ws_hub_std.pop_steal_until
      ctx.context_hub
      ctx.context_id
      max_round_noyield
      max_round_yield
      ~finished
      ~prepare_sleep
  with
  | None ->
      ()
  | Some job ->
      execute ctx job ;
      wait ctx ~finished ~prepare_sleep

let wait_on_ivar ctx ivar =
  let already_pushed = Atomic.make false in
  wait ctx
    ~finished:(fun () -> Ivar_3.is_set ivar)
    ~prepare_sleep:(fun wakeup ->
      if Atomic.exchange already_pushed true then (
        if Ivar_3.is_set ivar then false
        else true
      ) else (
        match Ivar_3.wait ivar (fun _ctx _v -> wakeup ()) with
          | None -> true
          | Some _v -> false
      )
    )
