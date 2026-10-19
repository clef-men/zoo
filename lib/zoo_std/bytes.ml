type t =
  bytes

let[@zoo.ignore] create =
  Stdlib.Bytes.create

let[@zoo.ignore] unsafe_get =
  Stdlib.Bytes.unsafe_get

let[@zoo.ignore] unsafe_set =
  Stdlib.Bytes.unsafe_set

let[@zoo.ignore] equal =
  Stdlib.Bytes.equal
