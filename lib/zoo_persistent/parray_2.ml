(* Based on:
   https://github.com/backtracking/spds/blob/12e48dc9f5d169ab38a9b7887bb481621ab04331/parray.ml
*)

type 'a descr =
  | Root
  | Diff of int * 'a * 'a node
and 'a node =
  'a descr ref

type 'a t =
  { equal: 'a -> 'a -> bool;
    data: 'a array;
    mutable root: 'a node;
  }

type 'a snapshot =
  'a node

let make equal sz v =
  let data = Array.unsafe_make sz v in
  let root = ref Root in
  { equal; data; root }

let get t i =
  Array.unsafe_get t.data i

let set t i v =
  let v' = Array.unsafe_get t.data i in
  if not @@ t.equal v v' then (
    let root = ref Root in
    t.root := Diff (i, v', root) ;
    t.root <- root ;
    Array.unsafe_set t.data i v
  )

let capture t =
  t.root

let rec restore data node =
  match !node with
  | Root ->
      ()
  | Diff (i, v, node') ->
      restore data node' ;
      node' := Diff (i, Array.unsafe_get data i, node) ;
      Array.unsafe_set data i v
let restore t s =
  match !s with
  | Root ->
      ()
  | Diff _ ->
      restore t.data s ;
      s := Root ;
      t.root <- s
