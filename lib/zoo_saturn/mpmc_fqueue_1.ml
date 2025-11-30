[@@@zoo.ignore]

type 'a t =
  { capacity: int;
    data: 'a Optional.t Atomic_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create cap =
  let data = Atomic_array.make cap Optional.Nothing in
  { capacity= cap;
    data;
    front= 0;
    back= 0;
  }

let make cap v =
  let data = Atomic_array.make cap Optional.Nothing in
  Atomic_array.unsafe_set data 0 (Something v) ;
  { capacity= cap;
    data;
    front= 0;
    back= 1;
  }

let is_empty t =
  let front = t.front in
  let back = t.back in
  back <= front

let push t v =
  if t.capacity <= t.back then
    false
  else
    let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
    let data = t.data in
    if t.capacity <= i then (
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
  if t.capacity <= t.front then
    None
  else
    let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
    if t.capacity <= i then
      None
    else
      pop t.data i
