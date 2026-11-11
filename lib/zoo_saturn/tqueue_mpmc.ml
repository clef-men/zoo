type 'a t =
  { capacity: int
  ; data: 'a Optional.t Atomic_array.t
  ; mutable front: int [@atomic]
  ; mutable back: int [@atomic]
  ; proph: (int * Zoo.id) Zoo.proph
  }

let create cap =
  let data = Atomic_array.make cap Optional.Nothing in
  { capacity= cap
  ; data
  ; front= 0
  ; back= 0
  ; proph= Zoo.proph ()
  }

let make cap v =
  let data = Atomic_array.make cap Optional.Nothing in
  Atomic_array.unsafe_set data 0 (Something v) ;
  { capacity= cap
  ; data
  ; front= 0
  ; back= 1
  ; proph= Zoo.proph ()
  }

let is_empty t =
  let front = t.front in
  let back = t.back in
  back <= front

let rec push t v =
  let id = Zoo.id () in
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  if t.capacity <= i then
    false
  else if Atomic_array.unsafe_cas_resolve t.data i Nothing (Something v) t.proph (i, id) then
    true
  else
    push t v
let push t v =
  if t.capacity <= t.back then
    false
  else
    push t v

let pop t =
  if t.capacity <= t.front then
    Optional.Anything
  else
    let id = Zoo.id () in
    let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
    if t.capacity <= i then
      Anything
    else
      Atomic_array.unsafe_xchg_resolve t.data i Anything t.proph (i, id)
