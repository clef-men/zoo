type t =
  string

let unsafe_get =
  Stdlib.String.unsafe_get
[@@zoo.ignore]

let equal =
  Stdlib.String.equal
[@@zoo.ignore]
