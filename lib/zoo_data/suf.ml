type descr =
  | Root of int
  | Link of element

and element =
  descr Sstore_2.ref

type t =
  Sstore_2.t

let create =
  Sstore_2.create

let make t =
  Sstore_2.ref t (Root 0)

let rec repr t elt =
  match Sstore_2.get t elt with
  | Root _ ->
      elt
  | Link parent ->
      let repr = repr t parent in
      Sstore_2.set t elt (Link repr) ;
      repr

let equiv t elt1 elt2 =
  repr t elt1 == repr t elt2

let[@inline] rank t elt =
  match Sstore_2.get t elt with
  | Root rank ->
      rank
  | Link _ ->
      assert false
let union t elt1 elt2 =
  let repr1 = repr t elt1 in
  let rank1 = rank t repr1 in
  let repr2 = repr t elt2 in
  let rank2 = rank t repr2 in
  if repr1 != repr2 then
    if rank1 < rank2 then (
      Sstore_2.set t repr1 (Link repr2)
    ) else (
      Sstore_2.set t repr2 (Link repr1) ;
      if rank1 == rank2 then
        Sstore_2.set t repr1 (Root (rank1 + 1))
    )

type snapshot =
  Sstore_2.snapshot

let capture =
  Sstore_2.capture

let restore =
  Sstore_2.restore
