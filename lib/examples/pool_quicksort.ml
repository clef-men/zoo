let rec main ctx arr i sz =
  if 1 < sz then
    let pivot = Array.partition arr i sz in
    Pool.async ctx (fun ctx -> main ctx arr i (pivot - i)) ;
    Pool.async ctx (fun ctx -> main ctx arr (pivot + 1) (sz - (pivot - i) - 1))
let main ctx arr =
  main ctx arr 0 (Array.size arr)

let main ~num_worker arr =
  Pool.run ~num_worker (fun ctx -> main ctx arr)
