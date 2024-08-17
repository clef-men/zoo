type t =
  Random.State.t

let[@zoo.assume] create =
  Stdlib.Random.State.make_self_init

let[@zoo.assume] gen =
  Stdlib.Random.State.int

let gen' t lb ub =
  lb + gen t (ub - lb)
