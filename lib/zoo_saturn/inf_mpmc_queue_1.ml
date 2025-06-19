type 'a t =
  { data: 'a Optional.t Inf_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create () =
  { data= Inf_array.create Optional.Nothing;
    front= 0;
    back= 0;
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

let push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  Inf_array.set t.data i (Something v)

let rec pop t i =
  match Inf_array.get t.data i with
  | Nothing ->
      Domain.yield () ;
      pop t i
  | Anything ->
      assert false
  | Something v ->
      Inf_array.set t.data i Anything ;
      v
let pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  pop t i
