type 'a t =
  { capacity: int;
    data: 'a array;
    mutable front: int;
    mutable back: int;
  }

let create cap =
  { capacity= cap;
    data= Array.unsafe_make cap (Obj.magic ());
    front= 0;
    back= 0;
  }

let size t =
  t.back - t.front

let is_empty t =
  size t == 0

let unsafe_get t i =
  Array.unsafe_cget t.data (t.front + i)

let unsafe_set t i v =
  Array.unsafe_cset t.data (t.front + i) v

let push t v =
  let front = t.front in
  let back = t.back in
  if front + t.capacity == back then (
    false
  ) else (
    Array.unsafe_cset t.data back v ;
    t.back <- back + 1 ;
    true
  )

let pop_front t =
  let front = t.front in
  let back = t.back in
  if front == back then
    None
  else
    let data = t.data in
    let v = Array.unsafe_cget data front in
    Array.unsafe_cset data front (Obj.magic ()) ;
    t.front <- front + 1 ;
    Some v

let pop_back t =
  let front = t.front in
  let back = t.back in
  if front == back then
    None
  else
    let data = t.data in
    let back = back - 1 in
    let v = Array.unsafe_cget data back in
    Array.unsafe_cset data back (Obj.magic ()) ;
    t.back <- back ;
    Some v
