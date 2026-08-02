type 'a node =
  { mutable prev: 'a node
  ; mutable next: 'a node
  ; mutable data: 'a
  }

type 'a t =
  'a node

let create () =
  let t =
    { prev= Obj.magic ()
    ; next= Obj.magic ()
    ; data= Obj.magic ()
    }
  in
  t.prev <- t ;
  t.next <- t ;
  t

let is_empty t =
  t.next == t

let link node1 node2 =
  node1.next <- node2 ;
  node2.prev <- node1

let insert prev node next =
  link prev node ;
  link node next

let push_front t front =
  insert t front t.next

let push_back t back =
  insert t.prev back t

let pop_front t =
  if is_empty t then
    None
  else
    let old_front = t.next in
    let front = old_front.next in
    link t front ;
    Some old_front

let pop_back t =
  if is_empty t then
    None
  else
    let old_back = t.prev in
    let back = old_back.prev in
    link back t ;
    Some old_back

let remove node =
  let prev = node.prev in
  let next = node.next in
  link prev next

let rec iter_aux fn t node =
  if node == t then (
    ()
  ) else (
    fn node ;
    iter_aux fn t node.next
  )
let iter fn t =
  iter_aux fn t t.next
