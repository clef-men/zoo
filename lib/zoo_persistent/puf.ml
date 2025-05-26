type descr =
  | Root of int
  | Link of element

and element =
  descr Pstore_2.ref

type t =
  descr Pstore_2.t

let create =
  Pstore_2.create

let make t =
  Pstore_2.ref t (Root 0)

let rec repr t elt =
  match Pstore_2.get t elt with
  | Root _ ->
      elt
  | Link parent ->
      let repr = repr t parent in
      Pstore_2.set t elt (Link repr) ;
      repr

let equiv t elt1 elt2 =
  repr t elt1 == repr t elt2

let[@inline] rank t elt =
  match Pstore_2.get t elt with
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
      Pstore_2.set t repr1 (Link repr2)
    ) else (
      Pstore_2.set t repr2 (Link repr1) ;
      if rank1 == rank2 then
        Pstore_2.set t repr1 (Root (rank1 + 1))
    )

type snapshot =
  descr Pstore_2.snapshot

let capture =
  Pstore_2.capture

let restore =
  Pstore_2.restore
