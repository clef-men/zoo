type 'a t =
  { mutable data: 'a array;
    default: 'a;
    mutex: Mutex.t;
  }

let create default =
  let data = Array.create () in
  let mutex = Mutex.create () in
  { data; default; mutex }

let next_capacity n =
  Int.max 8 (if n <= 512 then 2 * n else n + n / 2)
let reserve t n =
  let data = t.data in
  let cap = Array.size data in
  if cap < n then (
    let cap = Int.max n (next_capacity cap) in
    let data = Array.unsafe_grow data cap t.default in
    t.data <- data
  )

let get t i =
  Mutex.protect t.mutex @@ fun () ->
    let data = t.data in
    if i < Array.size data then (
      Array.unsafe_get data i
    ) else (
      t.default
    )

let set t i v =
  Mutex.protect t.mutex @@ fun () ->
    reserve t (i + 1) ;
    Array.unsafe_set t.data i v

let xchg t i v =
  Mutex.protect t.mutex @@ fun () ->
    reserve t (i + 1) ;
    let v' = Array.unsafe_get t.data i in
    Array.unsafe_set t.data i v ;
    v'

let cas t i v1 v2 =
  Mutex.protect t.mutex @@ fun () ->
    reserve t (i + 1) ;
    if Array.unsafe_get t.data i != v1 then (
      false
    ) else (
      Array.unsafe_set t.data i v2 ;
      true
    )

let faa t i incr =
  Mutex.protect t.mutex @@ fun () ->
    reserve t (i + 1) ;
    let n = Array.unsafe_get t.data i in
    Array.unsafe_set t.data i (n + incr) ;
    n
