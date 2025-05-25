(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

type 'a ref =
  'a Stdlib.ref

type 'a descr =
  | Root
  | Diff of 'a ref * 'a * 'a node
and 'a node =
  'a descr Stdlib.ref

type 'a t =
  'a node Stdlib.ref

type 'a snapshot =
  { snapshot_store: 'a t;
    snapshot_root: 'a node;
  }

let create () =
  Stdlib.ref (Stdlib.ref Root)

let ref _t v =
  Stdlib.ref v

let get _t r =
  !r

let set t r v =
  let root = Stdlib.ref Root in
  !t := Diff (r, !r, root) ;
  r := v ;
  t := root

let capture t =
  { snapshot_store= t;
    snapshot_root= !t;
  }

let rec collect node acc =
  match !node with
  | Root ->
      (node, acc)
  | Diff (_, _, node') ->
      collect node' (node :: acc)
let rec revert node = function
  | [] ->
      node := Root
  | node' :: path ->
      match !node' with
      | Root ->
          assert false
      | Diff (r, v, node_) ->
          assert (node_ == node) ;
          node := Diff (r, !r, node') ;
          r := v ;
          revert node' path
let reroot node =
  let root, nodes = collect node [] in
  revert root nodes

let restore t s =
  if t != s.snapshot_store then (
    assert false
  ) else (
    let root = s.snapshot_root in
    match !root with
    | Root ->
        ()
    | Diff _ ->
        reroot root ;
        t := root
  )
