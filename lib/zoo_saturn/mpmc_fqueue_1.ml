[@@@zoo.exclude]

type 'a t =
  { data: 'a Optional.t Atomic_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create sz =
  { data= Atomic_array.make sz Optional.Nothing;
    front= 0;
    back= 0;
  }

let make sz v =
  let data = Atomic_array.make sz Optional.Nothing in
  Atomic_array.unsafe_set data 0 (Something v) ;
  { data;
    front= 0;
    back= 1;
  }

let is_empty t =
  t.back <= t.front

let push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  let data = t.data in
  if Atomic_array.size data <= i then (
    false
  ) else (
    Atomic_array.unsafe_set data i (Something v) ;
    true
  )

let rec pop data i =
  match Atomic_array.unsafe_get data i with
  | Optional.Nothing ->
      Domain.yield () ;
      pop data i
  | Anything ->
      assert false
  | Something v ->
      Atomic_array.unsafe_set data i Anything ;
      Some v
let pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  let data = t.data in
  if Atomic_array.size data <= i then
    None
  else
    pop data i
