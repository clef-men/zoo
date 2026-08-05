(* Based on:
   https://gitlab.inria.fr/salto/salto-analyzer/-/blob/f75df173336d0671a38d6bb1fe7ab7a22bddc01a/src/domains/nablaRec/partition.ml
*)

type 'a elt =
  { mutable prev: 'a elt
  ; mutable next: 'a elt
  ; data: 'a
  ; mutable class_: 'a class_
  ; mutable seen: bool
  }

and 'a class_ =
  { mutable first: 'a elt
  ; mutable last: 'a elt
  ; mutable len: int
  ; mutable split: 'a elt
  ; mutable split_len: int
  }

module Dllist = struct
  let create v class_ =
    let elt =
      { prev= Obj.magic ()
      ; next= Obj.magic ()
      ; data= v
      ; class_
      ; seen= false
      }
    in
    elt.prev <- elt ;
    elt.next <- elt ;
    elt

  let link elt1 elt2 =
    elt1.next <- elt2 ;
    elt2.prev <- elt1

  let insert_right dst elt =
    link elt dst.next ;
    link dst elt

  let swap elt1 elt2 =
    if elt1 != elt2 then (
      let prev1 = elt1.prev in
      let next1 = elt1.next in
      let prev2 = elt2.prev in
      let next2 = elt2.next in
      if next1 == elt2 then (
        if next2 != elt1 then (
          link elt1 next2 ;
          link elt2 elt1 ;
          link prev1 elt2
        )
      ) else if prev1 == elt2 then (
        link prev2 elt1 ;
        link elt1 elt2 ;
        link elt2 next1
      ) else (
        link prev2 elt1 ;
        link elt1 next2 ;
        link elt2 next1 ;
        link prev1 elt2
      )
    )

  let rec iter fn from to_ =
    fn from ;
    if from != to_ then
      iter fn from.next to_
end

let class_is_singleton class_ =
  class_.len == 1
let class_add class_ elt =
  Dllist.insert_right class_.last elt ;
  class_.last <- elt ;
  class_.len <- class_.len + 1
let class_swap class_ elt1 elt2 =
  if elt1 != elt2 then (
    let first = class_.first in
    let last = class_.last in
    if first == elt1 then
      class_.first <- elt2
    else if first == elt2 then
      class_.first <- elt1 ;
    if last == elt2 then
      class_.last <- elt1
    else if last == elt1 then
      class_.last <- elt2 ;
    Dllist.swap elt1 elt2
  )
let class_iter fn class_ =
  Dllist.iter fn class_.first class_.last

let make v =
  let elt = Dllist.create v (Obj.magic ()) in
  let class_ =
    { first= elt
    ; last= elt
    ; len= 1
    ; split= elt
    ; split_len= 0
    }
  in
  elt.class_ <- class_ ;
  elt

let make_same_class elt v =
  let class_ = elt.class_ in
  let elt = Dllist.create v class_ in
  class_add class_ elt ;
  elt

let get elt =
  elt.data

let equal =
  (==)
let equiv elt1 elt2 =
  elt1.class_ == elt2.class_

let repr elt =
  elt.class_.first

let cardinal elt =
  elt.class_.len

let record split_list elt =
  let class_ = elt.class_ in
  if class_is_singleton class_ || elt.seen then (
    split_list
  ) else (
    elt.seen <- true ;
    let split = class_.split in
    if split == class_.last then (
      class_.split <- class_.first ;
      class_.split_len <- 0 ;
      split_list
    ) else (
      let record_class = split == class_.first in
      class_swap class_ split elt ;
      class_.split <- elt.next ;
      class_.split_len <- class_.split_len + 1 ;
      if record_class then
        class_ :: split_list
      else
        split_list
    )
  )
let record elts =
  List.foldl record [] elts

let split class_ =
  let first = class_.first in
  let split = class_.split in
  if split == first then (
    class_iter (fun elt -> elt.seen <- false) class_
  ) else (
    class_.first <- split ;
    class_.split <- split ;
    let split_len = class_.split_len in
    class_.split_len <- 0 ;
    class_.len <- class_.len - split_len ;
    let prev = split.prev in
    let class' =
      { first
      ; last= prev
      ; len= split_len
      ; split= first
      ; split_len= 0
      }
    in
    Dllist.iter (fun elt ->
      elt.class_ <- class' ;
      elt.seen <- false
    ) first prev
  )
let split split_list =
  List.iter split split_list

let refine elts =
  elts |> record |> split
