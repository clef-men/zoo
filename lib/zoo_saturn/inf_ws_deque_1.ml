(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/ws_deque.ml
*)

type 'a t =
  { mutable front: int [@atomic];
    mutable back: int [@atomic];
    data: 'a Inf_array.t;
    proph: (bool, int * Zoo.id) Zoo.proph;
  }

let create () =
  { front= 1;
    back= 1;
    data= Inf_array.create (Obj.magic ());
    proph= Zoo.proph ();
  }

let size t =
  t.back - t.front

let is_empty t =
  size t == 0

let push t v =
  let back = t.back in
  Inf_array.set t.data back v ;
  t.back <- back + 1

let rec steal t =
  let id = Zoo.id () in
  let front = t.front in
  let back = t.back in
  if back <= front then (
    None
  ) else if
    Zoo.resolve_with (
      Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
    ) t.proph (front, id)
  then (
    Some (Inf_array.get t.data front)
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
    Some (Inf_array.get t.data back)
  ) else (
    let won =
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
      ) t.proph (front, id)
    in
    t.back <- front + 1 ;
    if won then
      Some (Inf_array.get t.data front)
    else
      None
  )
let pop t =
  let id = Zoo.id () in
  let back = t.back - 1 in
  t.back <- back ;
  pop t id back
