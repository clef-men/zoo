type 'a t =
  { mutable size: int;
    mutable data: 'a array;
  }

let create () =
  { size= 0; data= Array.create () }

let make sz v =
  { size= sz; data= Array.unsafe_make sz v }

let initi sz fn =
  { size= sz; data= Array.unsafe_initi sz fn }

let size t =
  t.size
let capacity t =
  Array.size t.data

let is_empty t =
  size t == 0

let get t i =
  Array.unsafe_get t.data i

let set t i v =
  Array.unsafe_set t.data i v

let next_capacity n =
  Int.max 8 (if n <= 512 then 2 * n else n + n / 2)
let reserve t n =
  let data = t.data in
  let cap = Array.size data in
  if cap < n then (
    let new_cap = Int.max n (next_capacity cap) in
    let new_data = Array.unsafe_alloc new_cap in
    Array.unsafe_copy_slice data 0 new_data 0 t.size ;
    t.data <- new_data
  )
let reserve_extra t n =
  reserve t (t.size + n)

let grow t sz v =
  let old_sz = t.size in
  if old_sz < sz then (
    reserve t sz ;
    Array.unsafe_fill_slice t.data old_sz (sz - old_sz) v ;
    t.size <- sz
  )

let push t v =
  reserve_extra t 1 ;
  let sz = t.size in
  t.size <- sz + 1 ;
  Array.unsafe_set t.data sz v

let pop t =
  let sz = t.size - 1 in
  t.size <- sz ;
  let data = t.data in
  let v = Array.unsafe_get data sz in
  Array.unsafe_set data sz (Obj.magic ()) ;
  v

let fit_capacity t =
  let sz = t.size in
  let data = t.data in
  if sz != Array.size data then
    t.data <- Array.unsafe_shrink data sz

let reset t =
  t.size <- 0 ;
  t.data <- Array.create ()

let iteri fn t =
  Array.unsafe_iteri_slice fn t.data 0 t.size
let iter fn =
  iteri (fun _i -> fn)
