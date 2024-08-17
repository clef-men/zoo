type 'a t =
  { mutable head: 'a;
    mutable tail: 'a t;
  }

let cons head tail =
  { head; tail }

let head t =
  t.head
let tail t =
  t.tail

let set_head t head =
  t.head <- head
let set_tail t tail =
  t.tail <- tail
