type 'a snapshot =
  | Snapshot of 'a * int [@generative] [@zoo.generative_strong]

type 'a ref =
  { mutable ref_value: 'a [@atomic]
  ; mutable ref_snapshot: 'a snapshot [@atomic]
  }

type prophecy =
  | Forward : 'a ref * 'a * int -> prophecy
  | Get : 'a ref * Zoo.id -> prophecy
  | Set : 'a ref * Zoo.id * 'a -> prophecy
  | Xchg : 'a ref * Zoo.id * 'a -> prophecy
  | Cas : 'a ref * Zoo.id * 'a * 'a -> prophecy

type t =
  { mutable gen: int [@atomic]
  ; proph: prophecy Zoo.proph
  }

let create () =
  { gen= 0
  ; proph= Zoo.proph ()
  }

let ref _t v =
  { ref_value= v
  ; ref_snapshot= Snapshot (v, 0)
  }

let forward t r =
  let Snapshot (_, g_snap) as snap = r.ref_snapshot in
  let g = t.gen in
  if g_snap != g then
    let v = r.ref_value in
    if
      not @@
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set
          [%atomic.loc r.ref_snapshot]
          snap
          (Snapshot (v, g))
      ) t.proph (Forward (r, v, g))
    then
      let Snapshot (_, g_snap) as snap = r.ref_snapshot in
      let g = t.gen in
      if g_snap != g then
        let v = r.ref_value in
        Zoo.resolve_with (
          Atomic.Loc.compare_and_set
            [%atomic.loc r.ref_snapshot]
            snap
            (Snapshot (v, g))
        ) t.proph (Forward (r, v, g)) |> ignore

let get t r =
  let id = Zoo.id () in
  forward t r ;
  Zoo.resolve_with r.ref_value t.proph (Get (r, id))

let set t r v =
  let id = Zoo.id () in
  forward t r ;
  Zoo.resolve_with (r.ref_value <- v) t.proph (Set (r, id, v))

let xchg t r v =
  let id = Zoo.id () in
  forward t r ;
  Zoo.resolve_with (
    Atomic.Loc.exchange [%atomic.loc r.ref_value] v
  ) t.proph (Xchg (r, id, v))

let cas t r v1 v2 =
  let id = Zoo.id () in
  forward t r ;
  Zoo.resolve_with (
    Atomic.Loc.compare_and_set [%atomic.loc r.ref_value] v1 v2
  ) t.proph (Cas (r, id, v1, v2))

let click t =
  Atomic.Loc.incr [%atomic.loc t.gen]

let observe t r =
  forward t r ;
  let Snapshot (v, _) = r.ref_snapshot in
  v
