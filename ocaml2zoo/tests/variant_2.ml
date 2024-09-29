type 'a t =
  | Leaf
  | Node of 'a t * 'a * 'a t

let test1 () =
  let _ = Leaf in
  let _ = Node (Leaf, 0, Leaf) in
  let _ = Node (Node (Leaf, 0, Leaf), 1, Leaf) in
  ()

let rec test2 t =
  match t with
  | Leaf ->
      0
  | Node (t1, x, t2) ->
      test2 t1 + x + test2 t2
