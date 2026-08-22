type 'a t =
  'a Stdlib.Domain.t

let[@zoo.ignore] spawn =
  Stdlib.Domain.spawn

let[@zoo.ignore] join =
  Stdlib.Domain.join

let[@zoo.opaque] yield =
  Stdlib.Domain.cpu_relax

let[@zoo.opaque] self_index =
  Stdlib.Domain.self_index

let[@zoo.opaque] recommended_domain_count =
  Stdlib.Domain.recommended_domain_count

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
