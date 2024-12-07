(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/ws_deque.ml
*)

type 'a t =
  { mutable front: int [@atomic];
    mutable back: int [@atomic];
    data: 'a Inf_array.t;
    proph: (int * Zoo.id) Zoo.proph;
  }

let create () =
  { front= 0;
    back= 0;
    data= Inf_array.create (Obj.magic ());
    proph= Zoo.proph;
  }

let push t v =
  let back = t.back in
  Inf_array.set t.data back v ;
  t.back <- back + 1

let rec steal t =
  let id = Zoo.id in
  let front = t.front in
  let back = t.back in
  if back <= front then (
    None
  ) else if
    Zoo.resolve (
      Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
    ) t.proph (front, id)
  then (
    Some (Inf_array.get t.data front)
  ) else (
    Domain.cpu_relax () ;
    steal t
  )

let pop t =
  let id = Zoo.id in
  let back = t.back - 1 in
  t.back <- back ;
  let front = t.front in
  if back < front then (
    t.back <- front ;
    None
  ) else if front < back then (
    Some (Inf_array.get t.data back)
  ) else if
    Zoo.resolve (
      Atomic.Loc.compare_and_set [%atomic.loc t.front] front (front + 1)
    ) t.proph (front, id)
  then (
    t.back <- front + 1 ;
    Some (Inf_array.get t.data back)
  ) else (
    t.back <- front + 1 ;
    None
  )
