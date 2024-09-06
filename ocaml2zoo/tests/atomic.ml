let test () =
  let a = Atomic.make 0 in
  let _ = Atomic.exchange a 0 in
  let _ = Atomic.compare_and_set a 0 0 in
  let _ = Atomic.fetch_and_add a 0 in
  Atomic.decr a ;
  Atomic.incr a
