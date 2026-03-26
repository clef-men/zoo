let partition arr i sz =
  let pivot = Array.unsafe_get arr i in
  let i1 = ref (i + 1) in
  for i2 = i + 1 to i + sz do
    if Array.unsafe_get arr i2 < pivot then
      Array.unsafe_swap arr !i1 i2 ;
      i1 := !i1 + 1
  done ;
  Array.unsafe_swap arr i (!i1 - 1) ;
  !i1 - 1

let rec main ctx arr i sz =
  if 1 < sz then
    let pivot = partition arr i sz in
    Pool.async ctx (fun ctx -> main ctx arr i (pivot - i)) ;
    Pool.async ctx (fun ctx -> main ctx arr (pivot + 1) (sz - (pivot - i) - 1))
let main ctx arr =
  main ctx arr 0 (Array.size arr)

let main num_dom arr =
  let pool = Pool.create num_dom in
  Pool.run pool (fun ctx -> main ctx arr) ;
  Pool.kill pool
