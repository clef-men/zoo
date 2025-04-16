type 'a state =
  'a option

type 'a t =
  'a state Atomic.t

let create () =
  Atomic.make None

let try_get t =
  Atomic.get t

let is_set t =
  try_get t != None

let get t =
  match try_get t with
  | None ->
      assert false
  | Some v ->
      v

let set t v =
  Atomic.set t (Some v)
