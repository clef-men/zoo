(* Based on:
   https://gitlab.inria.fr/salto/salto-analyzer/-/blob/f75df173336d0671a38d6bb1fe7ab7a22bddc01a/src/domains/nablaRec/partition.ml
*)

type ('a, 'c) dllist =
  { mutable prev: ('a, 'c) dllist;
    mutable next: ('a, 'c) dllist;
    data: 'a;
    mutable class_: 'c;
    mutable seen: bool;
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

type 'a block =
  { mutable next_block: 'a block [@warning "-69"];
    mutable next_split: 'a block;
    mutable work_list_next: 'a block [@warning "-69"];
    mutable in_work_list: bool;
    mutable first: ('a, 'a block) dllist;
    mutable last: ('a, 'a block) dllist;
    mutable len: int;
    mutable split_start: ('a, 'a block) dllist;
    mutable split_len: int;
  }

let block_iter fn block =
  dllist_iter fn block.first block.last
let block_is_singleton block =
  block.len == 1
let block_swap block cell1 cell2 =
  if cell1 != cell2 then (
    let first = block.first in
    let last = block.last in
    if first == cell1 then
      block.first <- cell2
    else if first == cell2 then
      block.first <- cell1 ;
    if last == cell2 then
      block.last <- cell1
    else if last == cell1 then
      block.last <- cell2 ;
    dllist_swap cell1 cell2
  )
let block_record_split start_of_split_list cell =
  let block = cell.class_ in
  if block_is_singleton block || cell.seen then (
    start_of_split_list
  ) else (
    cell.seen <- true ;
    let cur_split_start = block.split_start in
    if cur_split_start == block.last then (
      block.split_start <- block.first ;
      block.split_len <- 0 ;
      start_of_split_list
    ) else (
      let never_split = cur_split_start == block.first in
      block_swap block cur_split_start cell ;
      block.split_start <- cell.next ;
      block.split_len <- block.split_len + 1 ;
      if never_split then (
        begin match start_of_split_list with
        | None ->
            ()
        | Some list_head ->
            block.next_split <- list_head
        end ;
        Some block
      ) else (
        start_of_split_list
      )
    )
  )

type 'a t =
  { mutable blocks_head: 'a block;
    mutable work_list_head: 'a block option;
  }

type 'a elt =
  ('a, 'a block) dllist

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
  let block =
    { next_block= Obj.magic ();
      next_split= Obj.magic ();
      work_list_next= Obj.magic ();
      in_work_list= true;
      first= elt;
      last= elt;
      len= 1;
      split_start= elt;
      split_len= 0;
    }
  in
  elt.prev <- elt ;
  elt.next <- elt ;
  elt.class_ <- block ;
  block.next_block <- block ;
  block.next_split <- block ;
  block.work_list_next <- block ;
  let t =
    { blocks_head= block;
      work_list_head= Some block;
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
  let block =
    { next_block= t.blocks_head;
      next_split= Obj.magic ();
      work_list_next= Obj.magic ();
      in_work_list= true;
      first= elt;
      last= elt;
      len= 1;
      split_start= elt;
      split_len= 0;
    }
  in
  elt.prev <- elt ;
  elt.next <- elt ;
  elt.class_ <- block ;
  block.next_split <- block ;
  block.work_list_next <- (match t.work_list_head with None -> block | Some wl -> wl) ;
  t.blocks_head <- block ;
  t.work_list_head <- Some block ;
  elt

let split_at elt_class t =
  let elt = elt_class.split_start in
  let elt_class_first = elt_class.first in
  if elt == elt_class_first then (
    block_iter (fun cell -> cell.seen <- false) elt_class
  ) else (
    let old_prev = elt.prev in
    elt_class.first <- elt ;
    elt_class.split_start <- elt ;
    let elt_class_split_len = elt_class.split_len in
    elt_class.split_len <- 0 ;
    elt_class.len <- elt_class.len - elt_class_split_len ;
    let class_descr =
      { next_block= t.blocks_head;
        next_split= Obj.magic ();
        work_list_next= Obj.magic ();
        in_work_list= false;
        first= elt_class_first;
        last= old_prev;
        len= elt_class_split_len;
        split_start= elt_class_first;
        split_len= 0;
      }
    in
    class_descr.next_split <- class_descr ;
    class_descr.work_list_next <- class_descr ;
    t.blocks_head <- class_descr ;
    if elt_class.in_work_list then (
      class_descr.in_work_list <- true ;
      begin match t.work_list_head with
      | None ->
          assert false
      | Some hd ->
          class_descr.work_list_next <- hd
      end ;
      t.work_list_head <- Some class_descr
    ) else (
      let selected_class =
        if elt_class.len <= class_descr.len then
          elt_class
        else
          class_descr
      in
      selected_class.in_work_list <- true ;
      begin match t.work_list_head with
      | None ->
          ()
      | Some hd ->
          selected_class.work_list_next <- hd
      end ;
      t.work_list_head <- Some selected_class
    ) ;
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
  match Lst.foldl elts None block_record_split with
  | None ->
      ()
  | Some split_list ->
      split_classes split_list t

(* let rec stabilize get_pre_images t = *)
(*   match t.work_list_head with *)
(*   | None -> *)
(*       () *)
(*   | Some hd -> *)
(*       t.work_list_head <- (if hd.work_list_next == hd then None else Some hd.work_list_next) ; *)
(*       hd.in_work_list <- false ; *)
(*       hd.work_list_next <- hd ; *)
(*       get_pre_images (fun fn -> block_iter fn hd) (refine t) ; *)
(*       stabilize get_pre_images t *)
