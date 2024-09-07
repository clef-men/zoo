type 'a t =
  'a array

let unsafe_alloc sz =
  Obj.magic (Obj.new_block 0 sz)
let alloc sz =
  if not (0 <= sz) then
    invalid_arg "negative size" ;
  unsafe_alloc sz

let create () =
  unsafe_alloc 0

let size t =
  Obj.(size @@ repr t)

let unsafe_get t i =
  Obj.(magic @@ field (repr t) i)
let get t i =
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (i < size t) then
    invalid_arg "index out of bounds" ;
  unsafe_get t i

let unsafe_set t i v =
  Obj.(set_field (repr t) i (repr v))
let set t i v =
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (i < size t) then
    invalid_arg "index out of bounds" ;
  unsafe_set t i v

let unsafe_fill_slice t i n v =
  for j = 0 to n - 1 do
    unsafe_set t (i + j) v
  done
let fill_slice t i n v =
  let sz = size t in
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (0 <= n) then
    invalid_arg "negative span" ;
  if not (i + n <= sz) then
    invalid_arg "invalid arguments" ;
  unsafe_fill_slice t i n v
let fill t v =
  unsafe_fill_slice t 0 (size t) v

let unsafe_make sz v =
  let t = unsafe_alloc sz in
  fill t v ;
  t
let make sz v =
  if not (0 <= sz) then
    invalid_arg "negative size" ;
  unsafe_make sz v

let rec foldli_aux t sz acc fn i =
  if sz <= i then (
    acc
  ) else (
    let v = unsafe_get t i in
    foldli_aux t sz (fn acc i v) fn (1 + i)
  )
let foldli t acc fn =
  foldli_aux t (size t) acc fn 0
let foldl t acc fn =
  foldli t acc (fun acc _ v -> fn acc v)

let rec foldri_aux t fn acc i =
  if i <= 0 then (
    acc
  ) else (
    let i = i - 1 in
    let v = unsafe_get t i in
    foldri_aux t fn (fn i v acc) i
  )
let foldri t fn acc =
  foldri_aux t fn acc (size t)
let foldr t fn acc =
  foldri t (fun _ -> fn) acc

let iteri t fn =
  for i = 0 to size t - 1 do
    fn i (unsafe_get t i)
  done
let iter t fn =
  iteri t (fun _ -> fn)

let applyi t fn =
  iteri t (fun i v -> unsafe_set t i (fn i v))
let apply t fn =
  applyi t (fun _ -> fn)

let unsafe_initi sz fn =
  let t = unsafe_alloc sz in
  applyi t (fun i _ -> fn i) ;
  t
let initi sz fn =
  if not (0 <= sz) then
    invalid_arg "negative size" ;
  unsafe_initi sz fn
let unsafe_init sz fn =
  unsafe_initi sz (fun _ -> fn ())
let init sz fn =
  if not (0 <= sz) then
    invalid_arg "negative size" ;
  unsafe_init sz fn

let mapi t fn =
  unsafe_initi (size t) (fun i -> fn i (unsafe_get t i))
let map t fn =
  mapi t (fun _ -> fn)

let unsafe_copy_slice t1 i1 t2 i2 n =
  for k = 0 to n - 1 do
    let v = unsafe_get t1 (i1 + k) in
    unsafe_set t2 (i2 + k) v
  done
let copy_slice t1 i1 t2 i2 n =
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 <= i1) then
    invalid_arg "negative index" ;
  if not (0 <= i2) then
    invalid_arg "negative index" ;
  if not (0 <= n) then
    invalid_arg "negative span" ;
  if not (i1 + n <= sz1) then
    invalid_arg "invalid arguments" ;
  if not (i2 + n <= sz2) then
    invalid_arg "invalid arguments" ;
  unsafe_copy_slice t1 i1 t2 i2 n
let unsafe_copy t1 t2 i2 =
  unsafe_copy_slice t1 0 t2 i2 (size t1)
let copy t1 t2 i2 =
  if not (0 <= i2) then
    invalid_arg "negative index" ;
  if not (i2 + size t1 <= size t2) then
    invalid_arg "invalid arguments" ;
  unsafe_copy t1 t2 i2

let unsafe_grow t sz' v' =
  let sz = size t in
  let t' = unsafe_alloc sz' in
  unsafe_copy t t' 0 ;
  unsafe_fill_slice t' sz (sz' - sz) v' ;
  t'
let grow t sz' v' =
  if not (size t <= sz') then
    invalid_arg "invalid size" ;
  unsafe_grow t sz' v'

let unsafe_sub t i n =
  let t' = unsafe_alloc n in
  unsafe_copy_slice t i t' 0 n ;
  t'
let sub t i n =
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (0 <= n) then
    invalid_arg "negative span" ;
  if not (i + n <= size t) then
    invalid_arg "invalid arguments" ;
  unsafe_sub t i n

let unsafe_shrink t sz' =
  unsafe_sub t 0 sz'
let shrink t sz' =
  if not (0 <= sz') then
    invalid_arg "negative size" ;
  if not (sz' <= size t) then
    invalid_arg "invalid size" ;
  unsafe_shrink t sz'

let clone t =
  unsafe_shrink t (size t)

let unsafe_cget t i =
  unsafe_get t (i mod size t)
let cget t i =
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (0 < size t) then
    invalid_arg "size must be strictly positive" ;
  unsafe_cget t i

let unsafe_cset t i v =
  unsafe_set t (i mod size t) v
let cset t i v =
  if not (0 <= i) then
    invalid_arg "negative index" ;
  if not (0 < size t) then
    invalid_arg "size must be strictly positive" ;
  unsafe_cset t i v

let unsafe_ccopy_slice t1 i1 t2 i2 n =
  for j = 0 to n - 1 do
    let v = unsafe_cget t1 (i1 + j) in
    unsafe_cset t2 (i2 + j) v
  done
let ccopy_slice t1 i1 t2 i2 n =
  if not (0 <= i1) then
    invalid_arg "negative index" ;
  if not (0 <= i2) then
    invalid_arg "negative index" ;
  if not (0 <= n) then
    invalid_arg "negative span" ;
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 < sz1) then
    invalid_arg "size must be strictly positive" ;
  if not (0 < sz2) then
    invalid_arg "size must be strictly positive" ;
  if not (n <= sz1) then
    invalid_arg "invalid span" ;
  if not (n <= sz2) then
    invalid_arg "invalid span" ;
  unsafe_ccopy_slice t1 i1 t2 i2 n

let unsafe_ccopy t1 i1 t2 i2 =
  unsafe_ccopy_slice t1 i1 t2 i2 (size t1)
let ccopy t1 i1 t2 i2 =
  if not (0 <= i1) then
    invalid_arg "negative index" ;
  if not (0 <= i2) then
    invalid_arg "negative index" ;
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 < sz1) then
    invalid_arg "size must be strictly positive" ;
  if not (sz1 <= sz2) then
    invalid_arg "invalid arguments" ;
  unsafe_ccopy t1 i1 t2 i2
