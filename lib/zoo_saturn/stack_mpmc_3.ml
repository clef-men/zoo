type 'a t =
  { stack: 'a Stack_mpmc_1.t
  ; channel: 'a Channel_sync_2.t
  ; mutable force_mutable: unit (* for verification *)
  }

let capacity_log =
  3

let create () =
  { stack= Stack_mpmc_1.create ()
  ; channel= Channel_sync_2.create ~cap_log:capacity_log
  ; force_mutable= ()
  }

let try_push t v =
  Stack_mpmc_1.try_push t.stack v ||
  Channel_sync_2.send t.channel v

let rec push t v backoff =
  if not @@ try_push t v then
    push t v (Backoff.once backoff)
let push t v =
  push t v Backoff.default

let try_pop t =
  match Stack_mpmc_1.try_pop t.stack with
  | Something _ as res ->
      res
  | Nothing ->
      Nothing
  | Anything ->
      match Channel_sync_2.recv t.channel with
      | Some v ->
          Something v
      | None ->
          Anything

let rec pop t backoff =
  match try_pop t with
  | Optional.Nothing ->
      None
  | Something v ->
      Some v
  | Anything ->
      pop t (Backoff.once backoff)
let pop t =
  pop t Backoff.default
