(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/michael_scott_queue/michael_scott_queue_unsafe.ml
*)

type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable next: ('a, [`Null | `Node]) node [@atomic];
      mutable data: 'a;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Node]) node [@atomic];
    mutable back: ('a, [`Node]) node [@atomic];
  }

let create () =
  let front = Node { next= Null; data= Obj.magic () } in
  { front; back= front }

let is_empty t =
  let Node front_r = t.front in
  front_r.next == Null

let rec push (node : (_, [`Node]) node) new_back =
  let Node node_r = node in
  match node_r.next with
  | Node _ as next ->
      push next new_back
  | Null ->
      if not @@ Atomic.Loc.compare_and_set [%atomic.loc node_r.next] Null new_back then (
        Domain.yield () ;
        push node new_back
      )
let rec fix_back t back new_back =
  let Node new_back_r = new_back in
  if new_back_r.next == Null
  && not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back
  then (
    Domain.yield () ;
    fix_back t t.back new_back
  )
let push t v =
  let (Node _ as new_back : (_, [`Node]) node) = Node { next= Null; data= v } in
  let back = t.back in
  push back new_back ;
  fix_back t back new_back

let rec pop t =
  let Node front_r as front = t.front in
  match front_r.next with
  | Null ->
      None
  | Node new_front_r as new_front ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
        let v = new_front_r.data in
        new_front_r.data <- Obj.magic () ;
        Some v
      ) else (
        Domain.yield () ;
        pop t
      )
