type 'a ref =
  'a Stdlib.ref

type 'a descr =
  | Root
  | Diff of 'a ref * 'a * 'a node
and 'a node =
  'a descr Stdlib.ref

type 'a t =
  'a node Stdlib.ref

type 'a snap =
  { snap_store: 'a t;
    snap_root: 'a node;
  }

let create () =
  Stdlib.ref (Stdlib.ref Root)

let ref v =
  Stdlib.ref v

let get _t r =
  !r

let set t r v =
  let root = Stdlib.ref Root in
  !t := Diff (r, !r, root) ;
  r := v ;
  t := root

let capture t =
  { snap_store= t; snap_root= !t }

let rec collect node acc =
  match !node with
  | Root ->
      (node, acc)
  | Diff (_, _, node') ->
      collect node' (node :: acc)
let rec revert node = function
  | [] ->
      node := Root
  | node' :: seg ->
      match !node' with
      | Root ->
          assert false
      | Diff (r, v, node_) ->
          assert (node_ == node) ;
          node := Diff (r, !r, node') ;
          r := v ;
          revert node' seg
let reroot node =
  let root, nodes = collect node [] in
  revert root nodes

let restore t s =
  if t != s.snap_store then (
    assert false
  ) else (
    let root = s.snap_root in
    match !root with
    | Root ->
        ()
    | Diff _ ->
        reroot root ;
        t := root
  )
