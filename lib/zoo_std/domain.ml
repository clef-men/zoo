type 'a t =
  'a Stdlib.Domain.t

let spawn =
  Stdlib.Domain.spawn
[@@zoo.ignore]

let join =
  Stdlib.Domain.join
[@@zoo.ignore]

let yield =
  Stdlib.Domain.cpu_relax
[@@zoo.opaque]

let self_index =
  Stdlib.Domain.self_index
[@@zoo.opaque]

let recommended_domain_count =
  Stdlib.Domain.recommended_domain_count
[@@zoo.opaque]

module Dls = struct
  type 'a key =
    'a Stdlib.Domain.DLS.key

  let new_key fn =
    Stdlib.Domain.DLS.new_key fn
  [@@zoo.ignore]

  let get =
    Stdlib.Domain.DLS.get
  [@@zoo.ignore]

  let set =
    Stdlib.Domain.DLS.set
  [@@zoo.ignore]
end
