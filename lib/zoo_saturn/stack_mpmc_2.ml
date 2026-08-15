type 'a t =
  'a Clist.t Atomic.t

let create () =
  Atomic.make Clist.Open

let rec push t v backoff =
  match Atomic.get t with
  | Clist.Closed ->
      true
  | _ as old ->
      let new_ = Clist.Cons (v, old) in
      if Atomic.compare_and_set t old new_ then
        false
      else
        push t v (Backoff.once backoff)
let push t v =
  push t v Backoff.default

let rec pop t backoff =
  match Atomic.get t with
  | Clist.Closed ->
      Optional.Anything
  | Open ->
      Nothing
  | Cons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then
        Something v
      else
        pop t (Backoff.once backoff)
let pop t =
  pop t Backoff.default

let is_closed t =
  Atomic.get t == Clist.Closed

let close t =
  Atomic.exchange t Clist.Closed
