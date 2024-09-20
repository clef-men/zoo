type 'a t =
  'a Clst.t Atomic.t

let create () =
  Atomic.make Clst.ClstOpen

let rec push t v =
  match Atomic.get t with
  | Clst.ClstClosed ->
      true
  | _ as old ->
      let new_ = Clst.ClstCons (v, old) in
      if Atomic.compare_and_set t old new_ then (
        false
      ) else (
        Domain.cpu_relax () ;
        push t v
      )

let rec pop t =
  match Atomic.get t with
  | Clst.ClstClosed ->
      Optional.Anything
  | ClstOpen ->
      Nothing
  | ClstCons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then (
        Something v
      ) else (
        Domain.cpu_relax () ;
        pop t
      )

let is_closed t =
  Atomic.get t == Clst.ClstClosed

let close t =
  Atomic.exchange t Clst.ClstClosed
