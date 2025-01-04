type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable next: ('a, [`Null | `Node]) node;
      mutable data: 'a;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Node]) node;
    mutable back: ('a, [`Node]) node;
  }

let create () =
  let front = Node { next= Null; data= Obj.magic () } in
  { front; back= front }

let is_empty t =
  t.front == t.back

let push t v =
  let (Node _ as new_back : (_, [`Node]) node) = Node { next= Null; data= Obj.magic () } in
  let Node back_r = t.back in
  back_r.next <- new_back ;
  back_r.data <- v ;
  t.back <- new_back

let pop t =
  let Node front_r = t.front in
  match front_r.next with
  | Null ->
      None
  | Node _ as next ->
      t.front <- next ;
      Some front_r.data
