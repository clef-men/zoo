type 'a node =
  { mutable xdeque_prev: 'a node;
    mutable xdeque_next: 'a node;
    mutable xdeque_data: 'a;
  }

type 'a t =
  'a node

let create () =
  let t = Obj.(magic @@ new_block 0 2) in
  t.xdeque_prev <- t ;
  t.xdeque_next <- t ;
  t

let is_empty t =
  t.xdeque_next == t

let link node1 node2 =
  node1.xdeque_next <- node2 ;
  node2.xdeque_prev <- node1

let insert prev node next =
  link prev node ;
  link node next

let push_front t front =
  insert t front t.xdeque_next

let push_back t back =
  insert t.xdeque_prev back t

let pop_front t =
  if is_empty t then
    None
  else
    let old_front = t.xdeque_next in
    let front = old_front.xdeque_next in
    link t front ;
    Some old_front

let pop_back t =
  if is_empty t then
    None
  else
    let old_back = t.xdeque_prev in
    let back = old_back.xdeque_prev in
    link back t ;
    Some old_back

let remove node =
  let prev = node.xdeque_prev in
  let next = node.xdeque_next in
  link prev next

let rec iter_aux fn t node =
  if node == t then (
    ()
  ) else (
    fn node ;
    iter_aux fn t node.xdeque_next
  )
let iter fn t =
  iter_aux fn t t.xdeque_next
