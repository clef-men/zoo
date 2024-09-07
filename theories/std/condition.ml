type t =
  Stdlib.Condition.t

let create =
  Stdlib.Condition.create
[@@zoo.override
  fun () ->
    ()
]

let wait =
  Stdlib.Condition.wait
[@@zoo.override
  fun t mtx ->
    Domain.cpu_relax ()
]

let notify =
  Stdlib.Condition.signal
[@@zoo.override
  fun () ->
    ()
]

let notify_all =
  Stdlib.Condition.broadcast
[@@zoo.override
  fun () ->
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
