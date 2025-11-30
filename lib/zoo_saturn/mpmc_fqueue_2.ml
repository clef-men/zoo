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

let rec push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  if t.capacity <= i then
    false
  else if Atomic_array.unsafe_cas t.data i Nothing (Something v) then
    true
  else
    push t v
let push t v =
  if t.capacity <= t.back then
    false
  else
    push t v

let rec pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  if t.capacity <= i then
    None
  else
    match Atomic_array.unsafe_xchg t.data i Anything with
    | Nothing ->
        Domain.yield () ;
        pop t
    | Anything ->
        assert false
    | Something v ->
        Some v
let pop t =
  if t.capacity <= t.front then
    None
  else
    pop t
