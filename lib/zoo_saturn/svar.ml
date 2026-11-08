type 'a snapshot =
  | Snapshot of 'a * int [@generative] [@zoo.generative_strong]

type prophecy =
  | Forward : 'a * int -> prophecy
  | Get : Zoo.id -> prophecy
  | Set : Zoo.id * 'a -> prophecy

type 'a t =
  { mutable value: 'a [@atomic]
  ; mutable gen: int [@atomic]
  ; mutable snapshot: 'a snapshot [@atomic]
  ; proph: prophecy Zoo.proph
  }

let make v =
  { value= v
  ; gen= 0
  ; snapshot= Snapshot (v, 0)
  ; proph= Zoo.proph ()
  }

let forward t =
  let Snapshot (_, g_snap) as snap = t.snapshot in
  let g = t.gen in
  if g_snap != g then
    let v = t.value in
    if
      not @@
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set
          [%atomic.loc t.snapshot]
          snap
          (Snapshot (v, g))
      ) t.proph (Forward (v, g))
    then
      let Snapshot (_, g_snap) as snap = t.snapshot in
      let g = t.gen in
      if g_snap != g then
        let v = t.value in
        Zoo.resolve_with (
          Atomic.Loc.compare_and_set
            [%atomic.loc t.snapshot]
            snap
            (Snapshot (v, g))
        ) t.proph (Forward (v, g)) |> ignore

let get t =
  let id = Zoo.id () in
  forward t ;
  Zoo.resolve_with t.value t.proph (Get id)

let set t v =
  let id = Zoo.id () in
  forward t ;
  Zoo.resolve_with (t.value <- v) t.proph (Set (id, v))

let click t =
  t.gen <- t.gen + 1

let observe t =
  forward t ;
  let Snapshot (v, _) = t.snapshot in
  v
