[@@@zoo.prefix pstore]

type gen =
  int

type 'a ref =
  { mutable ref_gen: gen;
    mutable ref_value: 'a;
  }

type 'a descr =
  | Root
  | Diff of 'a ref * gen * 'a * 'a node
and 'a node =
  'a descr Stdlib.ref

type 'a t =
  { mutable gen: gen;
    mutable root: 'a node;
  }

type 'a snap =
  { snap_store: 'a t;
    snap_gen: gen;
    snap_root: 'a node;
  }

let create () =
  { gen= 0; root= ref Root }

let ref t v =
  { ref_gen= 0; ref_value= v }

let get t r =
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
  t.gen <- 1 + g ;
  { snap_store= t; snap_gen= g; snap_root= t.root }

let rec collect node acc =
  match !node with
  | Root ->
      (node, acc)
  | Diff (_, _, _, node') ->
      collect node' (node :: acc)
let rec revert node path =
  match path with
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
  if t != s.snap_store then (
    assert false
  ) else (
    let root = s.snap_root in
    match !root with
    | Root ->
        ()
    | Diff (_, _, _, _) ->
        reroot root ;
        t.gen <- 1 + s.snap_gen ;
        t.root <- root
  )
