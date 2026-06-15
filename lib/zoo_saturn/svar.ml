type 'a snapshot =
  { snapshot_value: 'a
  ; snapshot_gen: int
  }

type prophecy =
  | Forward : 'a * int -> prophecy
  | Set : Zoo.id * 'a -> prophecy

type 'a t =
  { mutable value: 'a [@atomic]
  ; mutable gen: int [@atomic]
  ; mutable snapshot: 'a snapshot [@atomic]
  ; proph: prophecy Zoo.proph
  }

let make v =
  let snap = { snapshot_value= v; snapshot_gen= 0 } in
  { value= v
  ; gen= 0
  ; snapshot= snap
  ; proph= Zoo.proph ()
  }

let forward t =
  let snap = t.snapshot in
  let g = t.gen in
  if snap.snapshot_gen != g then
    let v = t.value in
    let snap' = { snapshot_value= v; snapshot_gen= g } in
    if
      not @@
      Zoo.resolve_with (
        Atomic.Loc.compare_and_set
          [%atomic.loc t.snapshot]
          snap
          snap'
      ) t.proph (Forward (v, g))
    then
      let snap = t.snapshot in
      let g = t.gen in
      if snap.snapshot_gen != g then
        let v = t.value in
        let snap' = { snapshot_value= v; snapshot_gen= g } in
        Zoo.resolve_with (
          Atomic.Loc.compare_and_set
            [%atomic.loc t.snapshot]
            snap
            snap'
        ) t.proph (Forward (v, g)) |> ignore

let get t =
  forward t ;
  t.value

let set t v =
  let id = Zoo.id () in
  forward t ;
  Zoo.resolve_with (t.value <- v) t.proph (Set (id, v))

let click t =
  t.gen <- t.gen + 1

let observe t =
  forward t ;
  t.snapshot.snapshot_value
