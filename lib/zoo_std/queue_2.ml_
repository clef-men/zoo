type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable head: 'a;
      mutable tail: ('a, [`Null | `Node]) node;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Node]) node;
    mutable sentinel: ('a, [`Node]) node;
  }

let create () =
  let sent = Node { head= Obj.magic (); tail= Null } in
  { front= sent; sentinel= sent }

let is_empty t =
  t.front == t.sentinel

let push t v =
  let (Node _ as new_sent : (_, [`Node]) node) = Node { head= Obj.magic (); tail= Null } in
  let Node sent_r = t.sentinel in
  sent_r.head <- v ;
  sent_r.tail <- new_sent ;
  t.sentinel <- new_sent

let pop t =
  let Node front_r = t.front in
  match front_r.tail with
  | Null ->
      None
  | Node _ as tail ->
      t.front <- tail ;
      Some front_r.head
