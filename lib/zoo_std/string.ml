type t =
  string

let[@zoo.ignore] unsafe_get =
  Stdlib.String.unsafe_get

let[@zoo.ignore] equal =
  Stdlib.String.equal
