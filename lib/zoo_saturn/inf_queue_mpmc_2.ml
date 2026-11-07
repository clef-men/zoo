type 'a t =
  { data: 'a Optional.t Inf_array.t
  ; mutable front: int [@atomic]
  ; mutable back: int [@atomic]
  ; proph: (int * Zoo.id) Zoo.proph
  }

let create () =
  { data= Inf_array.create Optional.Nothing
  ; front= 0
  ; back= 0
  ; proph= Zoo.proph ()
  }

let rec size t =
  let front = t.front in
  let proph = Zoo.proph () in
  let back = t.back in
  if Zoo.resolve proph t.front == front then
    Int.positive_part (back - front)
  else
    size t

let is_empty t =
  let front = t.front in
  let back = t.back in
  back <= front

let rec push t v =
  let id = Zoo.id () in
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  if not @@ Inf_array.cas_resolve t.data i Nothing (Something v) t.proph (i, id) then
    push t v

let try_pop_once t =
  let id = Zoo.id () in
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  match Inf_array.xchg_resolve t.data i Anything t.proph (i, id) with
  | Nothing ->
      None
  | Anything ->
      assert false
  | Something v ->
      Some v

let rec pop t backoff =
  match try_pop_once t with
  | None ->
      pop t (Backoff.once backoff)
  | Some v ->
      v
let pop t =
  pop t Backoff.default

let rec try_pop t backoff =
  if is_empty t then
    None
  else
    match try_pop_once t with
    | None ->
        try_pop t (Backoff.once backoff)
    | Some _ as res ->
        res
let try_pop t =
  try_pop t Backoff.default
