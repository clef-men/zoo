type 'a t =
  'a Stdlib.Domain.t

type 'a key =
  'a Stdlib.Domain.DLS.key

let[@zoo.exclude] spawn =
  Stdlib.Domain.spawn

let[@zoo.exclude] join =
  Stdlib.Domain.join

let[@zoo.exclude] local_new fn =
  Stdlib.Domain.DLS.new_key fn

let[@zoo.exclude] local_get =
  Stdlib.Domain.DLS.get

let[@zoo.exclude] local_set =
  Stdlib.Domain.DLS.set

let[@zoo.opaque] yield =
  Stdlib.Domain.cpu_relax

let[@zoo.opaque] self_index =
  Stdlib.Domain.self_index

let[@zoo.opaque] recommended_domain_count =
  Stdlib.Domain.recommended_domain_count
