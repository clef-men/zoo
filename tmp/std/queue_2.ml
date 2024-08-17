type ('a, _) mlist =
  | Mnil :
    ('a, [> `Nil]) mlist
  | Mcons :
    { mutable head: 'a;
      mutable tail: ('a, [`Nil | `Cons]) mlist;
    } ->
    ('a, [> `Cons]) mlist

type 'a t =
  { mutable front: ('a, [`Cons]) mlist;
    mutable sentinel: ('a, [`Cons]) mlist;
  }

let create () =
  let sent = Mcons { head= Obj.magic (); tail= Mnil } in
  { front= sent; sentinel= sent }

let is_empty t =
  t.front == t.sentinel

let push t v =
  let sent = Mcons { head= Obj.magic (); tail= Mnil } in
  let Mcons cons = t.sentinel in
  cons.head <- v ;
  cons.tail <- sent ;
  t.sentinel <- sent

let pop t =
  let Mcons cons = t.front in
  match cons.tail with
  | Mnil ->
      None
  | Mcons _ as tail ->
      t.front <- tail ;
      Some cons.head
