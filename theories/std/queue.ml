type 'a t =
  { mutable front: 'a Chain.t;
    mutable sentinel: 'a Chain.t;
  }

let create () =
  let sent = Chain.{ chain_head= Obj.magic (); chain_tail= Obj.magic () } in
  { front= sent; sentinel= sent }

let is_empty t =
  t.front == t.sentinel

let push t v =
  let sent = Chain.{ chain_head= Obj.magic (); chain_tail= Obj.magic () } in
  t.sentinel.chain_head <- v ;
  t.sentinel.chain_tail <- sent ;
  t.sentinel <- sent

let pop t =
  if is_empty t then (
    None
  ) else (
    let v = t.front.chain_head in
    t.front <- t.front.chain_tail ;
    Some v
  )
