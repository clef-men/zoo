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
    mutable back: ('a, [`Node]) node;
  }

let create () =
  let front = Node { next= Null; data= Obj.magic () } in
  { front; back= front }

let is_empty t =
  let Node front_r = t.front in
  front_r.next == Null

let push t v =
  let (Node _ as new_back : (_, [`Node]) node) = Node { next= Null; data= v } in
  let Node back_r = t.back in
  back_r.next <- new_back ;
  t.back <- new_back

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
