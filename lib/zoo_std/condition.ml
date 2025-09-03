type t =
  Stdlib.Condition.t

let create =
  Stdlib.Condition.create
[@@zoo.overwrite
  fun () ->
    ()
]

let notify =
  Stdlib.Condition.signal
[@@zoo.overwrite
  fun _t ->
    ()
]

let notify_all =
  Stdlib.Condition.broadcast
[@@zoo.overwrite
  fun _t ->
    ()
]

let wait =
  Stdlib.Condition.wait
[@@zoo.overwrite
  fun _t _mtx ->
    ()
]

let rec wait_until_aux t mtx pred =
  if not @@ pred () then (
    wait t mtx ;
    wait_until_aux t mtx pred
  )
let wait_until t mtx pred =
  wait_until_aux t mtx pred

let wait_while t mtx pred =
  wait_until t mtx (fun _ -> not @@ pred ())
