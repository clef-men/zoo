type t =
  { size: int;
    data: float array;
  }

let create sz =
  { size= sz;
    data= Array.create_float (sz * sz);
  }

let[@inline] size t =
  t.size

let[@inline] row sz idx =
  idx / sz

let[@inline] col sz idx =
  idx mod sz

let[@inline] index t i j =
  i * t.size + j

let get t i j =
  Array.unsafe_get t.data (index t i j)
let set t i j v =
  Array.unsafe_set t.data (index t i j) v

module Parallel
  (Pool : Pool.S)
= struct
  let fill ctx t v =
    let sz = t.size in
    let data = t.data in
    Pool.divide ctx ~beg:0 ~end_:(sz * sz) (fun _ctx idx sz ->
      Array.fill data idx sz v
    )

  let copy ctx t =
    let sz = t.size in
    let data = t.data in
    let data' = Array.create_float (sz * sz) in
    Pool.divide ctx ~beg:0 ~end_:(sz * sz) (fun _ctx idx n ->
      Array.blit data idx data' idx n
    ) ;
    { size= sz; data= data' }

  let apply ctx t fn =
    let sz = t.size in
    let data = t.data in
    Pool.for_ ctx ~beg:0 ~end_:(sz * sz) (fun _ctx idx ->
      fn (row sz idx) (col sz idx)
      |> Array.unsafe_set data idx
    )
end
