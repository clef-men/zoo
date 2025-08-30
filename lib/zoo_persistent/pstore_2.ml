(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

type gen =
  int

type 'a ref =
  { mutable ref_gen: gen;
    mutable ref_value: 'a;
  }

type descr =
  | Root
  | Diff : 'a ref * gen * 'a * node -> descr
and node =
  descr Stdlib.ref

type t =
  { mutable gen: gen;
    mutable root: node;
  }

type snapshot =
  { snapshot_store: t;
    snapshot_gen: gen;
    snapshot_root: node;
  }

let create () =
  { gen= 0; root= ref Root }

let ref _t v =
  { ref_gen= 0; ref_value= v }

let get _t r =
  r.ref_value

let set t r v =
  let g_t = t.gen in
  let g_r = r.ref_gen in
  if g_t == g_r then (
    r.ref_value <- v
  ) else (
    let root = Stdlib.ref Root in
    t.root := Diff (r, g_r, r.ref_value, root) ;
    r.ref_gen <- g_t ;
    r.ref_value <- v ;
    t.root <- root
  )

let capture t =
  let g = t.gen in
  t.gen <- g + 1 ;
  { snapshot_store= t;
    snapshot_gen= g;
    snapshot_root= t.root;
  }

let rec collect node path =
  match !node with
  | Root ->
      node, path
  | Diff (_, _, _, node') ->
      collect node' (node :: path)
let rec revert node = function
  | [] ->
      node := Root
  | node' :: path ->
      match !node' with
      | Root ->
          assert false
      | Diff (r, g, v, node_) ->
          assert (node_ == node) ;
          node := Diff (r, r.ref_gen, r.ref_value, node') ;
          r.ref_gen <- g ;
          r.ref_value <- v ;
          revert node' path
let reroot node =
  let root, path = collect node [] in
  revert root path

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
        t.gen <- s.snapshot_gen + 1 ;
        t.root <- root
  )
