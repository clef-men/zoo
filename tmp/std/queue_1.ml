type 'a t =
  { front: 'a Chain.t;
    sentinel: 'a Chain.t;
  }

let create () =
  let sent = Chain.cons (Obj.magic ()) (Obj.magic ()) in
  { front= sent; sentinel= sent }

let is_empty t =
  t.front == t.sentinel

let push t v =
  let sent = Chain.cons (Obj.magic ()) (Obj.magic ()) in
  Chain.set_head t.sentinel v ;
  Chain.set_tail t.sentinel sent ;
  t.sentinel <- sent

let pop t =
  if is_empty t then (
    None
  ) else (
    let v = Chain.head t.front in
    t.front <- Chain.tail t.front ;
    Some v
  )
