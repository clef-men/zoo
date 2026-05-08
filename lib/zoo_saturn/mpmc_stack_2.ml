type 'a t =
  'a Clist.t Atomic.t

let create () =
  Atomic.make Clist.ClistOpen

let rec push t v =
  match Atomic.get t with
  | Clist.ClistClosed ->
      true
  | _ as old ->
      let new_ = Clist.ClistCons (v, old) in
      if Atomic.compare_and_set t old new_ then (
        false
      ) else (
        Domain.yield () ;
        push t v
      )

let rec pop t =
  match Atomic.get t with
  | Clist.ClistClosed ->
      Optional.Anything
  | ClistOpen ->
      Nothing
  | ClistCons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then (
        Something v
      ) else (
        Domain.yield () ;
        pop t
      )

let is_closed t =
  Atomic.get t == Clist.ClistClosed

let close t =
  Atomic.exchange t Clist.ClistClosed
