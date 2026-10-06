type 'a t =
  { exchangers: 'a Exchanger_1.t array
  ; capacity_log: int
  }

let create ~cap_log =
  { exchangers= Array.unsafe_init (1 lsl cap_log) Exchanger_1.create
  ; capacity_log= cap_log
  }

let rec exchange t v log =
  if t.capacity_log < log then
    None
  else
    let i = Random.int (1 lsl log) in
    let exchanger = Array.unsafe_get t.exchangers i in
    match Exchanger_1.exchange exchanger v with
    | None ->
        exchange t v (log + 1)
    | Some _ as res ->
        res
let exchange t v =
  exchange t v 0
