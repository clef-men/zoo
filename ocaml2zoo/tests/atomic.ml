let test1 () =
  let a = Atomic.make 0 in
  let _ = Atomic.exchange a 0 in
  let _ = Atomic.compare_and_set a 0 0 in
  let _ = Atomic.fetch_and_add a 0 in
  Atomic.decr a ;
  Atomic.incr a

let test2 loc =
  let _ = Atomic.Loc.get loc in
  let _ = Atomic.Loc.set loc 0 in
  let _ = Atomic.Loc.exchange loc 0 in
  let _ = Atomic.Loc.compare_and_set loc 0 0 in
  let _ = Atomic.Loc.fetch_and_add loc 0 in
  Atomic.Loc.decr loc ;
  Atomic.Loc.incr loc

type 'a t =
  { mutable f: 'a [@atomic];
  }

let test3 t =
  let _ = Atomic.Loc.get [%atomic.loc t.f] in
  let _ = Atomic.Loc.set [%atomic.loc t.f] 0 in
  let _ = Atomic.Loc.exchange [%atomic.loc t.f] 0 in
  let _ = Atomic.Loc.compare_and_set [%atomic.loc t.f] 0 0 in
  let _ = Atomic.Loc.fetch_and_add [%atomic.loc t.f] 0 in
  Atomic.Loc.decr [%atomic.loc t.f] ;
  Atomic.Loc.incr [%atomic.loc t.f]
