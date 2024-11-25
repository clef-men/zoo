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
  let cell =
    { prev= Obj.magic ();
      next= Obj.magic ();
      data= v;
      class_;
      seen= false;
    }
  in
  cell.prev <- cell ;
  cell.next <- cell ;
  cell
let dllist_link cell1 cell2 =
  cell1.next <- cell2 ;
  cell2.prev <- cell1
let dllist_insert_right dst cell =
  dllist_link cell dst.next ;
  dllist_link dst cell
let dllist_swap cell1 cell2 =
  if cell1 != cell2 then (
    let prev1 = cell1.prev in
    let next1 = cell1.next in
    let prev2 = cell2.prev in
    let next2 = cell2.next in
    if next1 == cell2 then (
      if next2 != cell1 then (
        dllist_link cell1 next2 ;
        dllist_link cell2 cell1 ;
        dllist_link prev1 cell2
      )
    ) else if prev1 == cell2 then (
      dllist_link prev2 cell1 ;
      dllist_link cell1 cell2 ;
      dllist_link cell2 next1
    ) else (
      dllist_link prev2 cell1 ;
      dllist_link cell1 next2 ;
      dllist_link cell2 next1 ;
      dllist_link prev1 cell2
    )
  )
let rec dllist_iter fn from to_ =
  fn from ;
  if from != to_ then
    dllist_iter fn from.next to_

let class_iter fn class_ =
  dllist_iter fn class_.first class_.last
let class_is_singleton class_ =
  class_.len == 1
let class_swap class_ cell1 cell2 =
  if cell1 != cell2 then (
    let first = class_.first in
    let last = class_.last in
    if first == cell1 then
      class_.first <- cell2
    else if first == cell2 then
      class_.first <- cell1 ;
    if last == cell2 then
      class_.last <- cell1
    else if last == cell1 then
      class_.last <- cell2 ;
    dllist_swap cell1 cell2
  )
let class_record_split start_of_split_list cell =
  let class_ = cell.class_ in
  if class_is_singleton class_ || cell.seen then (
    start_of_split_list
  ) else (
    cell.seen <- true ;
    let cur_split_start = class_.split_start in
    if cur_split_start == class_.last then (
      class_.split_start <- class_.first ;
      class_.split_len <- 0 ;
      start_of_split_list
    ) else (
      let never_split = cur_split_start == class_.first in
      class_swap class_ cur_split_start cell ;
      class_.split_start <- cell.next ;
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

type 'a t =
  { mutable classes_head: 'a class_;
  }

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
  let t =
    { classes_head= class_;
    }
  in
  t, elt

let add_same_class elt v =
  let class_ = elt.class_ in
  let cell = dllist_create v class_ in
  dllist_insert_right class_.last cell ;
  class_.last <- cell ;
  class_.len <- class_.len + 1 ;
  cell

let add_new_class t v =
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
  t.classes_head <- class_ ;
  elt

let split_at elt_class t =
  let elt = elt_class.split_start in
  let elt_class_first = elt_class.first in
  if elt == elt_class_first then (
    class_iter (fun cell -> cell.seen <- false) elt_class
  ) else (
    let old_prev = elt.prev in
    elt_class.first <- elt ;
    elt_class.split_start <- elt ;
    let elt_class_split_len = elt_class.split_len in
    elt_class.split_len <- 0 ;
    elt_class.len <- elt_class.len - elt_class_split_len ;
    let class_descr =
      { next_split= Obj.magic ();
        first= elt_class_first;
        last= old_prev;
        len= elt_class_split_len;
        split_start= elt_class_first;
        split_len= 0;
      }
    in
    class_descr.next_split <- class_descr ;
    t.classes_head <- class_descr ;
    dllist_iter (fun elt ->
      elt.class_ <- class_descr ;
      elt.seen <- false
    ) elt_class_first old_prev
  )

let split_class class_ t =
  split_at class_ t ;
  class_.split_start <- class_.first ;
  class_.next_split <- class_

let rec split_classes class_ t =
  let next = class_.next_split in
  split_class class_ t ;
  if next != class_ then
    split_classes next t

let refine t elts =
  match Lst.foldl class_record_split None elts with
  | None ->
      ()
  | Some split_list ->
      split_classes split_list t
