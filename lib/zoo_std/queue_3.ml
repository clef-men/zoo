type 'a t =
  { mutable data: 'a array;
    mutable front: int;
    mutable back: int;
  }

let min_capacity =
  16

let create () =
  { data= Array.unsafe_make min_capacity (Obj.magic ());
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

let next_capacity n =
  Int.max 8 (if n <= 512 then 2 * n else n + n / 2)
let grow t =
  let front = t.front in
  let back = t.back in
  let data = t.data in
  let cap = Array.size data in
  if front + cap == back then
    let new_cap = Int.max (cap + 1) (next_capacity cap) in
    let new_data = Array.unsafe_cgrow data front new_cap (Obj.magic ()) in
    t.data <- new_data

let push t v =
  grow t ;
  let back = t.back in
  Array.unsafe_cset t.data back v ;
  t.back <- back + 1

let shrink t =
  let front = t.front in
  let back = t.back in
  let sz = back - front in
  let data = t.data in
  let cap = Array.size data in
  if min_capacity + 3 * sz <= cap then
    let new_cap = cap lsr 1 + 1 in
    let new_data = Array.unsafe_cshrink_slice data front new_cap in
    t.data <- new_data

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
    shrink t ;
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
    shrink t ;
    Some v
