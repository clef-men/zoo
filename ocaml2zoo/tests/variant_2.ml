type 'a t =
  | Leaf
  | Node of 'a t * 'a * 'a t

let test () =
  let _ = Leaf in
  let _ = Node (Leaf, 0, Leaf) in
  let _ = Node (Node (Leaf, 0, Leaf), 1, Leaf) in
  ()
