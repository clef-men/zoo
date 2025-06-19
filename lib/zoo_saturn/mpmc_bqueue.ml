(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/bounded_queue/bounded_queue.body.ml
*)

type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable next: ('a, [`Null | `Node]) node [@atomic];
      mutable data: 'a;
      mutable index: int;
      mutable estimated_capacity: int;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { capacity: int;
    mutable front: ('a, [`Node]) node [@atomic];
    mutable back: ('a, [`Node]) node [@atomic];
  }

let create cap =
  let front =
    Node {
      next= Null;
      data= Obj.magic ();
      index= 0;
      estimated_capacity= cap;
    }
  in
  { capacity= cap; front; back= front }

let capacity t =
  t.capacity

let rec size t =
  let (Node front_r as front) = t.front in
  let proph = Zoo.proph () in
  let (Node back_r as back) = t.back in
  match back_r.next with
  | Node _ as node ->
      Atomic.Loc.compare_and_set [%atomic.loc t.back] back node |> ignore ;
      size t
  | Null ->
      if Zoo.resolve_with t.front proph () == front then
        back_r.index - front_r.index
      else
        size t

let is_empty t =
  let Node front_r = t.front in
  front_r.next == Null

let rec fix_back t back new_back =
  let Node new_back_r = new_back in
  if new_back_r.next == Null
  && not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back
  then (
    Domain.yield () ;
    fix_back t t.back new_back
  )
let rec push_1 t back cap (new_back : (_, [`Node]) node) =
  let Node back_r = back in
  let (Node new_back_r as new_back) = new_back in
  if cap == 0 then (
    let Node front_r = t.front in
    let cap = t.capacity - (back_r.index - front_r.index) in
    if cap == 0 then (
      false
    ) else (
      back_r.estimated_capacity <- cap ;
      push_1 t back cap new_back
    )
  ) else (
    new_back_r.index <- back_r.index + 1 ;
    new_back_r.estimated_capacity <- cap - 1 ;
    if Atomic.Loc.compare_and_set [%atomic.loc back_r.next] Null new_back then (
      fix_back t back new_back ;
      true
    ) else (
      match back_r.next with
      | Null ->
          assert false
      | Node _ as back ->
          push_2 t back new_back
    )
  )
and push_2 t (back : (_, [`Node]) node) new_back =
  let Node back_r as back = back in
  push_1 t back back_r.estimated_capacity new_back
let push t v =
  let new_back =
    Node {
      next= Null;
      data= v;
      index= 0;
      estimated_capacity= 0;
    }
  in
  push_2 t t.back new_back

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
