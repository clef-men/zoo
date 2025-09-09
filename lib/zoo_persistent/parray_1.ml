(* Based on:
   https://github.com/backtracking/spds/blob/12e48dc9f5d169ab38a9b7887bb481621ab04331/parray.ml
*)

type 'a descr =
  | Root of
    { equal: 'a -> 'a -> bool;
      data: 'a array;
    }
  | Diff of int * 'a * 'a t
and 'a t =
  'a descr ref

let make equal sz v =
  let data = Array.unsafe_make sz v in
  ref (Root { equal; data })

let rec reroot t =
  match !t with
  | Root root_r ->
      root_r.equal, root_r.data
  | Diff (i, v, t') ->
      let equal, data = reroot t' in
      t' := Diff (i, Array.unsafe_get data i, t) ;
      Array.unsafe_set data i v ;
      equal, data
let reroot t =
  match !t with
  | Root root_r ->
      root_r.equal, root_r.data
  | Diff _ ->
      let equal, data = reroot t in
      t := Root { equal; data } ;
      equal, data

let get t i =
  let _, data = reroot t in
  Array.unsafe_get data i

let set t i v =
  let equal, data = reroot t in
  let v' = Array.unsafe_get data i in
  if equal v v' then (
    t
  ) else (
    Array.unsafe_set data i v ;
    let t' = ref !t in
    t := Diff (i, v', t') ;
    t'
  )
