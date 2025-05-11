type 'a t =
  'a array

let unsafe_alloc sz =
  Obj.magic (Obj.new_block 0 sz)
let alloc sz =
  if not (0 <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": negative size" ;
  unsafe_alloc sz

let create () =
  [||]
[@@zoo.overwrite
  fun () ->
    unsafe_alloc 0
]

let size =
  Stdlib.Array.length
[@@zoo.overwrite
  fun t ->
    Obj.(size @@ repr t)
]

let unsafe_get =
  Stdlib.Array.unsafe_get
[@@zoo.overwrite
  fun t i ->
    Obj.(magic @@ field (repr t) i)
]
let get =
  Stdlib.Array.get
[@@zoo.overwrite
  fun t i ->
    if not (0 <= i) then
      invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
    if not (i < size t) then
      invalid_arg @@ __FUNCTION__ ^ ": index out of bounds" ;
    unsafe_get t i
]

let unsafe_set =
  Stdlib.Array.unsafe_set
[@@zoo.overwrite
  fun t i v ->
    Obj.(set_field (repr t) i (repr v))
]
let set =
  Stdlib.Array.set
[@@zoo.overwrite
  fun t i v ->
    if not (0 <= i) then
      invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
    if not (i < size t) then
      invalid_arg @@ __FUNCTION__ ^ ": index out of bounds" ;
    unsafe_set t i v
]

let unsafe_fill_slice t i n v =
  for j = 0 to n - 1 do
    unsafe_set t (i + j) v
  done
let fill_slice t i n v =
  let sz = size t in
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  if not (i + n <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_fill_slice t i n v
let fill t v =
  unsafe_fill_slice t 0 (size t) v

let unsafe_make sz v =
  let t = unsafe_alloc sz in
  fill t v ;
  t
let make =
  Stdlib.Array.make
[@@zoo.overwrite
  fun sz v ->
    if not (0 <= sz) then
      invalid_arg @@ __FUNCTION__ ^ ": negative size" ;
    unsafe_make sz v
]

let rec foldli_aux fn t sz i acc =
  if sz <= i then (
    acc
  ) else (
    let v = unsafe_get t i in
    foldli_aux fn t sz (i + 1) (fn i acc v)
  )
let foldli fn acc t =
  foldli_aux fn t (size t) 0 acc
let foldl fn =
  foldli (fun _i -> fn)

let rec foldri_aux fn t i acc =
  if i <= 0 then (
    acc
  ) else (
    let i = i - 1 in
    let v = unsafe_get t i in
    foldri_aux fn t i (fn i v acc)
  )
let foldri fn t acc =
  foldri_aux fn t (size t) acc
let foldr fn =
  foldri (fun _i -> fn)

let sum t =
  foldl (+) 0 t

let unsafe_iteri_slice fn t i n =
  for k = 0 to n - 1 do
    fn k (unsafe_get t (i + k))
  done
let iteri_slice fn t i n =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  let sz = size t in
  if not (i <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid index" ;
  if not (i + n <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_iteri_slice fn t i n
let unsafe_iter_slice fn =
  unsafe_iteri_slice (fun _i -> fn)
let iter_slice fn t i n =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  let sz = size t in
  if not (i <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid index" ;
  if not (i + n <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_iter_slice fn t i n
let iteri fn t =
  unsafe_iteri_slice fn t 0 (size t)
let iter fn =
  iteri (fun _i -> fn)

let unsafe_applyi_slice fn t i n =
  unsafe_iteri_slice (fun k v -> unsafe_set t (i + k) (fn k v)) t i n
let applyi_slice fn t i n =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  let sz = size t in
  if not (i <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid index" ;
  if not (i + n <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_applyi_slice fn t i n
let unsafe_apply_slice fn =
  unsafe_applyi_slice (fun _i -> fn)
let apply_slice fn t i n =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  let sz = size t in
  if not (i <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid index" ;
  if not (i + n <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_apply_slice fn t i n
let applyi fn t =
  unsafe_applyi_slice fn t 0 (size t)
let apply fn =
  applyi (fun _i -> fn)

let unsafe_initi sz fn =
  let t = unsafe_alloc sz in
  applyi (fun i _ -> fn i) t ;
  t
let initi sz fn =
  if not (0 <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": negative size" ;
  unsafe_initi sz fn
let unsafe_init sz fn =
  unsafe_initi sz (fun _i -> fn ())
let init sz fn =
  if not (0 <= sz) then
    invalid_arg @@ __FUNCTION__ ^ ": negative size" ;
  unsafe_init sz fn

let mapi fn t =
  unsafe_initi (size t) (fun i -> fn i (unsafe_get t i))
let map fn =
  mapi (fun _i -> fn)

let unsafe_copy_slice t1 i1 t2 i2 n =
  for k = 0 to n - 1 do
    let v = unsafe_get t1 (i1 + k) in
    unsafe_set t2 (i2 + k) v
  done
let copy_slice t1 i1 t2 i2 n =
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 <= i1) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= i2) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  if not (i1 + n <= sz1) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  if not (i2 + n <= sz2) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_copy_slice t1 i1 t2 i2 n
let unsafe_copy t1 t2 i2 =
  unsafe_copy_slice t1 0 t2 i2 (size t1)
let copy t1 t2 i2 =
  if not (0 <= i2) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (i2 + size t1 <= size t2) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_copy t1 t2 i2

let unsafe_grow t sz' v' =
  let sz = size t in
  let t' = unsafe_alloc sz' in
  unsafe_copy t t' 0 ;
  unsafe_fill_slice t' sz (sz' - sz) v' ;
  t'
let grow t sz' v' =
  if not (size t <= sz') then
    invalid_arg @@ __FUNCTION__ ^ ": invalid size" ;
  unsafe_grow t sz' v'

let unsafe_sub t i n =
  let t' = unsafe_alloc n in
  unsafe_copy_slice t i t' 0 n ;
  t'
let sub t i n =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  if not (i + n <= size t) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_sub t i n

let unsafe_shrink t sz' =
  unsafe_sub t 0 sz'
let shrink t sz' =
  if not (0 <= sz') then
    invalid_arg @@ __FUNCTION__ ^ ": negative size" ;
  if not (sz' <= size t) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid size" ;
  unsafe_shrink t sz'

let clone t =
  unsafe_shrink t (size t)

let unsafe_cget t i =
  unsafe_get t (i mod size t)
let cget t i =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 < size t) then
    invalid_arg @@ __FUNCTION__ ^ ": size must be strictly positive" ;
  unsafe_cget t i

let unsafe_cset t i v =
  unsafe_set t (i mod size t) v
let cset t i v =
  if not (0 <= i) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 < size t) then
    invalid_arg @@ __FUNCTION__ ^ ": size must be strictly positive" ;
  unsafe_cset t i v

let unsafe_ccopy_slice t1 i1 t2 i2 n =
  for j = 0 to n - 1 do
    let v = unsafe_cget t1 (i1 + j) in
    unsafe_cset t2 (i2 + j) v
  done
let ccopy_slice t1 i1 t2 i2 n =
  if not (0 <= i1) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= i2) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= n) then
    invalid_arg @@ __FUNCTION__ ^ ": negative span" ;
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 < sz1) then
    invalid_arg @@ __FUNCTION__ ^ ": size must be strictly positive" ;
  if not (0 < sz2) then
    invalid_arg @@ __FUNCTION__ ^ ": size must be strictly positive" ;
  if not (n <= sz1) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid span" ;
  if not (n <= sz2) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid span" ;
  unsafe_ccopy_slice t1 i1 t2 i2 n

let unsafe_ccopy t1 i1 t2 i2 =
  unsafe_ccopy_slice t1 i1 t2 i2 (size t1)
let ccopy t1 i1 t2 i2 =
  if not (0 <= i1) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  if not (0 <= i2) then
    invalid_arg @@ __FUNCTION__ ^ ": negative index" ;
  let sz1 = size t1 in
  let sz2 = size t2 in
  if not (0 < sz1) then
    invalid_arg @@ __FUNCTION__ ^ ": size must be strictly positive" ;
  if not (sz1 <= sz2) then
    invalid_arg @@ __FUNCTION__ ^ ": invalid arguments" ;
  unsafe_ccopy t1 i1 t2 i2

let unsafe_cgrow_slice t i n sz' v =
  let t' = unsafe_make sz' v in
  unsafe_ccopy_slice t i t' i n ;
  t'
let unsafe_cgrow t i sz' v =
  unsafe_cgrow_slice t i (size t) sz' v

let unsafe_cshrink_slice t i sz' =
  let t' = unsafe_alloc sz' in
  unsafe_ccopy_slice t i t' i sz' ;
  t'
