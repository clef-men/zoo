type 'a t =
  'a Stdlib.Domain.t

let[@zoo.ignore] spawn =
  Stdlib.Domain.spawn

let[@zoo.ignore] join =
  Stdlib.Domain.join

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

  let[@zoo.ignore] new_key fn =
    Stdlib.Domain.DLS.new_key fn

  let[@zoo.ignore] get =
    Stdlib.Domain.DLS.get

  let[@zoo.ignore] set =
    Stdlib.Domain.DLS.set
end
