type 'a t =
  { capacity: int;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
    data: 'a Array.t;
    proph: (bool, int * Zoo.id) Zoo.proph;
  }

let create cap =
  { capacity= cap;
    front= 1;
    back= 1;
    data= Array.unsafe_make cap (Obj.magic ());
    proph= Zoo.proph ();
  }

let capacity t =
  t.capacity

let push t v =
  let front = t.front in
  let back = t.back in
  let data = t.data in
  let cap = Array.size data in
  if back < front + cap then (
    Array.unsafe_cset data back v ;
    t.back <- back + 1 ;
    true
  ) else (
    false
  )

let rec steal t =
  let id = Zoo.id () in
  let front = t.front in
  let back = t.back in
  if back <= front then
    None
  else
    let data = t.data in
    let v = Array.unsafe_cget data front in
    if
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
      ) t.proph (front, id)
    then (
      Some v
    ) else (
      Domain.yield () ;
      steal t
    )

let[@inline] pop t id back =
  let front = t.front in
  if back < front then (
    t.back <- front ;
    None
  ) else if front < back then (
    Some (Array.unsafe_cget t.data back)
  ) else (
    let won =
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
      ) t.proph (front, id)
    in
    t.back <- front + 1 ;
    if won then
      Some (Array.unsafe_cget t.data front)
    else
      None
  )
let pop t =
  let id = Zoo.id () in
  let back = t.back - 1 in
  t.back <- back ;
  pop t id back
