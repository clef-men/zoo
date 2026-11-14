type t =
  bytes

let create =
  Stdlib.Bytes.create
[@@zoo.ignore]

let unsafe_get =
  Stdlib.Bytes.unsafe_get
[@@zoo.ignore]

let unsafe_set =
  Stdlib.Bytes.unsafe_set
[@@zoo.ignore]

let equal =
  Stdlib.Bytes.equal
[@@zoo.ignore]
