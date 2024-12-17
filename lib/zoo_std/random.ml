let[@zoo.opaque] init =
  Stdlib.Random.self_init

let[@zoo.opaque] bits () =
  Stdlib.Random.nativebits ()
  |> Nativeint.to_int

let[@zoo.opaque] int =
  Stdlib.Random.int

let int_in_range lb ub =
  lb + int (ub - lb)
