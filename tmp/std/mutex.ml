type t =
  Stdlib.Mutex.t

let create =
  Stdlib.Mutex.create
[@@zoo.override
  fun () ->
    Atomic.make false
]

let lock =
  Stdlib.Mutex.lock
[@@zoo.override
let rec lock t =
  if not @@ Atomic.compare_and_set t false true then (
    Domain.cpu_relax () ;
    lock t
  )
]

let unlock =
  Stdlib.Mutex.unlock
[@@zoo.override
  fun t ->
    Atomic.set t false
]

let protect =
  Stdlib.Mutex.protect
[@@zoo.override
  fun t fn ->
    lock t ;
    let res = fn () in
    unlock t ;
    res
]
