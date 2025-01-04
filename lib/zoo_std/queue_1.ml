type 'a t =
  { mutable front: 'a Chain.t;
    mutable back: 'a Chain.t;
  }

let create () =
  let front = Chain.{ chain_next= Obj.magic (); chain_data= Obj.magic () } in
  { front; back= front }

let is_empty t =
  t.front == t.back

let push t v =
  let back = t.back in
  let new_back = Chain.{ chain_next= Obj.magic (); chain_data= Obj.magic () } in
  back.chain_next <- new_back ;
  back.chain_data <- v ;
  t.back <- new_back

let pop t =
  if is_empty t then (
    None
  ) else (
    let front = t.front in
    t.front <- front.chain_next ;
    let v = front.chain_data in
    Some v
  )
