(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/ws_deque.ml
*)

type 'a t =
  { mutable front: int [@atomic];
    mutable back: int [@atomic];
    mutable data: 'a array [@atomic];
    proph: (int * Zoo.id) Zoo.proph;
  }

let[@zoo.opaque] min_capacity =
  1 lsl 4

let create () =
  { front= 0;
    back= 0;
    data= Array.unsafe_make min_capacity (Obj.magic ());
    proph= Zoo.proph ();
  }

let push t v =
  let front = t.front in
  let back = t.back in
  let data = t.data in
  let cap = Array.size data in
  if back < front + cap then (
    Array.unsafe_cset data back v
  ) else (
    let new_cap = cap lsl 1 in
    let new_data = Array.unsafe_cgrow_slice data front (back - front) new_cap (Obj.magic ()) in
    Array.unsafe_cset new_data back v ;
    t.data <- new_data
  ) ;
  t.back <- back + 1

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
      Zoo.resolve (
        Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
      ) t.proph (front, id)
    then (
      Some v
    ) else (
      Domain.yield () ;
      steal t
    )

let pop t =
  let id = Zoo.id () in
  let back = t.back - 1 in
  t.back <- back ;
  let front = t.front in
  if back < front then (
    t.back <- front ;
    None
  ) else if front < back then (
    let data = t.data in
    let cap = Array.size data in
    let v = Array.unsafe_cget data back in
    let sz = back - front in
    if min_capacity + 3 * sz <= cap then (
      let new_cap = cap lsr 1 in
      let new_data = Array.unsafe_cshrink_slice data front new_cap in
      t.data <- new_data
    ) ;
    Some v
  ) else (
    let won =
      Zoo.resolve (
        Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
      ) t.proph (front, id)
    in
    t.back <- front + 1 ;
    if won then
      let data = t.data in
      let v = Array.unsafe_cget data back in
      Some v
    else
      None
  )
