type 'a t =
  { mutable front: 'a Chain.t
  ; mutable back: 'a Chain.t
  }

let create () =
  let front = Chain.{ next= Obj.magic (); data= Obj.magic () } in
  { front; back= front }

let is_empty t =
  t.front == t.back

let push t v =
  let back = t.back in
  let new_back = Chain.{ next= Obj.magic (); data= Obj.magic () } in
  back.next <- new_back ;
  back.data <- v ;
  t.back <- new_back

let pop t =
  if is_empty t then (
    None
  ) else (
    let front = t.front in
    t.front <- front.next ;
    let v = front.data in
    Some v
  )
