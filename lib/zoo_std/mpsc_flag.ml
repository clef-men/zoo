type t =
  bool Atomic.t

let create () =
  Atomic.make false

let get =
  Atomic.get

let set t =
  Atomic.set t true
