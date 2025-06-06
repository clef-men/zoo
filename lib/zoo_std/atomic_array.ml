type 'a t =
  'a Stdlib.Atomic_array.t

let make =
  Stdlib.Atomic_array.make
[@@zoo.overwrite_raw "zoo_std.array.array_make"]

let init sz fn =
  Stdlib.Atomic_array.init sz (fun _i -> fn ())
[@@zoo.overwrite_raw "zoo_std.array.array_init"]
let initi =
  Stdlib.Atomic_array.init
[@@zoo.overwrite_raw "zoo_std.array.array_initi"]

let size =
  Stdlib.Atomic_array.length
[@@zoo.overwrite_raw "zoo_std.array.array_size"]

let unsafe_get =
  Stdlib.Atomic_array.unsafe_get
[@@zoo.overwrite_raw "zoo_std.array.array_unsafe_get"]
let get =
  Stdlib.Atomic_array.get
[@@zoo.overwrite_raw "zoo_std.array.array_get"]

let unsafe_set =
  Stdlib.Atomic_array.unsafe_set
[@@zoo.overwrite_raw "zoo_std.array.array_unsafe_set"]
let set =
  Stdlib.Atomic_array.set
[@@zoo.overwrite_raw "zoo_std.array.array_set"]

let unsafe_xchg =
  Stdlib.Atomic_array.unsafe_exchange
[@@zoo.overwrite_raw "zoo_std.array.array_unsafe_xchg"]

let unsafe_cas =
  Stdlib.Atomic_array.unsafe_compare_and_set
[@@zoo.overwrite_raw "zoo_std.array.array_unsafe_cas"]

let unsafe_faa =
  Stdlib.Atomic_array.unsafe_fetch_and_add
[@@zoo.overwrite_raw "zoo_std.array.array_unsafe_faa"]

let[@zoo.ignore] rec foldli_aux fn t sz i acc =
  if sz <= i then (
    acc
  ) else (
    let v = unsafe_get t i in
    foldli_aux fn t sz (i + 1) (fn i acc v)
  )
let foldli fn acc t =
  foldli_aux fn t (size t) 0 acc
[@@zoo.overwrite_raw "zoo_std.array.array_foldli"]
let foldl fn =
  foldli (fun _i -> fn)
[@@zoo.overwrite_raw "zoo_std.array.array_foldl"]

let sum t =
  foldl (+) 0 t
[@@zoo.overwrite_raw "zoo_std.array.array_sum"]
