type 'a descr =
  | Root of 'a array
  | Diff of int * 'a * 'a t
and 'a t =
  'a descr ref

let make sz v =
  ref (Root (Array.make sz v))

let rec reroot t =
  match !t with
  | Root arr ->
      arr
  | Diff (i, v, t') ->
      let arr = reroot t' in
      t' := Diff (i, Array.unsafe_get arr i, t) ;
      Array.unsafe_set arr i v ;
      t := Root arr ;
      arr

let get t i =
  Array.unsafe_get (reroot t) i

let set t eq i v =
  let arr = reroot t in
  let v' = Array.unsafe_get arr i in
  if eq v v' then (
    t
  ) else (
    Array.unsafe_set arr i v ;
    let t' = ref !t in
    t := Diff (i, v', t') ;
    t'
  )
