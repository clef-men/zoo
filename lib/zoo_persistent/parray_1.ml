(* Based on:
   https://github.com/backtracking/spds/blob/12e48dc9f5d169ab38a9b7887bb481621ab04331/parray.ml
*)

type 'a descr =
  | Root of 'a array
  | Diff of int * 'a * 'a t
and 'a t =
  'a descr ref

let make sz v =
  ref (Root (Array.unsafe_make sz v))

let rec reroot t =
  match !t with
  | Root data ->
      data
  | Diff (i, v, t') ->
      let data = reroot t' in
      t' := Diff (i, Array.unsafe_get data i, t) ;
      Array.unsafe_set data i v ;
      data
let reroot t =
  match !t with
  | Root data ->
      data
  | Diff _ ->
      let data = reroot t in
      t := Root data ;
      data

let get t i =
  let data = reroot t in
  Array.unsafe_get data i

let set t equal i v =
  let data = reroot t in
  let v' = Array.unsafe_get data i in
  if equal v v' then (
    t
  ) else (
    Array.unsafe_set data i v ;
    let t' = ref !t in
    t := Diff (i, v', t') ;
    t'
  )
