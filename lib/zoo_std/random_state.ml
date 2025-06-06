type t =
  Stdlib.Random.State.t

let[@zoo.opaque] create =
  Stdlib.Random.State.make_self_init

let[@zoo.opaque] bits t =
  t
  |> Stdlib.Random.State.nativebits
  |> Nativeint.to_int

let[@zoo.opaque] int =
  Stdlib.Random.State.int

let int_in_range t lb ub =
  lb + int t (ub - lb)
