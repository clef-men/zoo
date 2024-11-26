(* Based on:
   https://gitlab.inria.fr/salto/salto-analyzer/-/blob/f75df173336d0671a38d6bb1fe7ab7a22bddc01a/src/domains/nablaRec/partition.ml
*)

type 'a dllist =
  { mutable prev: 'a dllist;
    mutable next: 'a dllist;
    data: 'a;
    mutable class_: 'a class_;
    mutable seen: bool;
  }

and 'a class_ =
  { mutable next_split: 'a class_;
    mutable first: 'a dllist;
    mutable last: 'a dllist;
    mutable len: int;
    mutable split_start: 'a dllist;
    mutable split_len: int;
  }

let dllist_create v class_ =
  let elt =
    { prev= Obj.magic ();
      next= Obj.magic ();
      data= v;
      class_;
      seen= false;
    }
  in
  elt.prev <- elt ;
  elt.next <- elt ;
  elt
let dllist_link elt1 elt2 =
  elt1.next <- elt2 ;
  elt2.prev <- elt1
let dllist_insert_right dst elt =
  dllist_link elt dst.next ;
  dllist_link dst elt
let dllist_swap elt1 elt2 =
  if elt1 != elt2 then (
    let prev1 = elt1.prev in
    let next1 = elt1.next in
    let prev2 = elt2.prev in
    let next2 = elt2.next in
    if next1 == elt2 then (
      if next2 != elt1 then (
        dllist_link elt1 next2 ;
        dllist_link elt2 elt1 ;
        dllist_link prev1 elt2
      )
    ) else if prev1 == elt2 then (
      dllist_link prev2 elt1 ;
      dllist_link elt1 elt2 ;
      dllist_link elt2 next1
    ) else (
      dllist_link prev2 elt1 ;
      dllist_link elt1 next2 ;
      dllist_link elt2 next1 ;
      dllist_link prev1 elt2
    )
  )
let rec dllist_iter fn from to_ =
  fn from ;
  if from != to_ then
    dllist_iter fn from.next to_

let class_is_singleton class_ =
  class_.len == 1
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
    dllist_swap elt1 elt2
  )
let class_iter fn class_ =
  dllist_iter fn class_.first class_.last

type 'a elt =
  'a dllist

let elt_equal =
  (==)
let elt_equiv elt1 elt2 =
  elt1.class_ == elt2.class_
let elt_repr elt =
  elt.class_.first
let elt_get elt =
  elt.data
let elt_cardinal elt =
  elt.class_.len

let create v =
  let elt =
    { prev= Obj.magic ();
      next= Obj.magic ();
      data= v;
      class_= Obj.magic ();
      seen= false;
    }
  in
  let class_ =
    { next_split= Obj.magic ();
      first= elt;
      last= elt;
      len= 1;
      split_start= elt;
      split_len= 0;
    }
  in
  elt.prev <- elt ;
  elt.next <- elt ;
  elt.class_ <- class_ ;
  class_.next_split <- class_ ;
  elt

let add_same_class elt v =
  let class_ = elt.class_ in
  let elt = dllist_create v class_ in
  dllist_insert_right class_.last elt ;
  class_.last <- elt ;
  class_.len <- class_.len + 1 ;
  elt

let add_new_class v =
  let elt =
    { prev= Obj.magic ();
      next= Obj.magic ();
      data= v;
      class_= Obj.magic ();
      seen= false;
    }
  in
  let class_ =
    { next_split= Obj.magic ();
      first= elt;
      last= elt;
      len= 1;
      split_start= elt;
      split_len= 0;
    }
  in
  elt.prev <- elt ;
  elt.next <- elt ;
  elt.class_ <- class_ ;
  class_.next_split <- class_ ;
  elt

let record_split start_of_split_list elt =
  let class_ = elt.class_ in
  if class_is_singleton class_ || elt.seen then (
    start_of_split_list
  ) else (
    elt.seen <- true ;
    let cur_split_start = class_.split_start in
    if cur_split_start == class_.last then (
      class_.split_start <- class_.first ;
      class_.split_len <- 0 ;
      start_of_split_list
    ) else (
      let never_split = cur_split_start == class_.first in
      class_swap class_ cur_split_start elt ;
      class_.split_start <- elt.next ;
      class_.split_len <- class_.split_len + 1 ;
      if never_split then (
        begin match start_of_split_list with
        | None ->
            ()
        | Some list_head ->
            class_.next_split <- list_head
        end ;
        Some class_
      ) else (
        start_of_split_list
      )
    )
  )

let split_class class_ =
  let elt = class_.split_start in
  let first = class_.first in
  if elt == first then (
    class_iter (fun elt -> elt.seen <- false) class_
  ) else (
    let prev = elt.prev in
    class_.first <- elt ;
    let split_len = class_.split_len in
    class_.split_len <- 0 ;
    class_.len <- class_.len - split_len ;
    let class_descr =
      { next_split= Obj.magic ();
        first;
        last= prev;
        len= split_len;
        split_start= first;
        split_len= 0;
      }
    in
    class_descr.next_split <- class_descr ;
    dllist_iter (fun elt ->
      elt.class_ <- class_descr ;
      elt.seen <- false
    ) first prev
  )

let rec split_classes class_ =
  let next = class_.next_split in
  split_class class_ ;
  class_.split_start <- class_.first ;
  class_.next_split <- class_ ;
  if next != class_ then
    split_classes next

let refine elts =
  match Lst.foldl record_split None elts with
  | None ->
      ()
  | Some split_list ->
      split_classes split_list
