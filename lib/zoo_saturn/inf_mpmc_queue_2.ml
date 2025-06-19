type 'a t =
  { data: 'a Optional.t Inf_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
    proph: (int * Zoo.id) Zoo.proph';
  }

let create () =
  { data= Inf_array.create Optional.Nothing;
    front= 0;
    back= 0;
    proph= Zoo.proph ();
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
  size t == 0

let rec push t v =
  let id = Zoo.id () in
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  if not @@ Inf_array.cas_resolve t.data i Nothing (Something v) t.proph (i, id) then
    push t v

let rec pop t =
  let id = Zoo.id () in
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  match Inf_array.xchg_resolve t.data i Anything t.proph (i, id) with
  | Nothing ->
      Domain.yield () ;
      pop t
  | Anything ->
      assert false
  | Something v ->
      v
