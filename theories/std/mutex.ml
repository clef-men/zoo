type t =
  Stdlib.Mutex.t

let create =
  Stdlib.Mutex.create
[@@zoo.overwrite
  fun () ->
    Atomic.make false
]

let rec lock =
  Stdlib.Mutex.lock
[@@zoo.overwrite
  fun t ->
    if not @@ Atomic.compare_and_set t false true then (
      Domain.cpu_relax () ;
      lock t
    )
]

let unlock =
  Stdlib.Mutex.unlock
[@@zoo.overwrite
  fun t ->
    Atomic.set t false
]

let protect =
  Stdlib.Mutex.protect
[@@zoo.overwrite
  fun t fn ->
    lock t ;
    let res = fn () in
    unlock t ;
    res
]
