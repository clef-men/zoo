type ('context, 'a) t =
  ('a, 'context -> 'a -> unit) Ivar_3.t

type ('context, 'a) waiter =
  'context -> 'a -> unit

let create =
  Ivar_3.create

let make =
  Ivar_3.make

let is_unset =
  Ivar_3.is_unset
let is_set =
  Ivar_3.is_set

let try_get =
  Ivar_3.try_get
let get =
  Ivar_3.get

let wait =
  Ivar_3.wait

let set =
  Ivar_3.set

let notify t ctx v =
  let waiters = set t v in
  Lst.iter (fun waiter -> waiter ctx v) waiters
