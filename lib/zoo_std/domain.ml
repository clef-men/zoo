type 'a t =
  'a Stdlib.Domain.t

let[@zoo.exclude] spawn =
  Stdlib.Domain.spawn

let[@zoo.exclude] join =
  Stdlib.Domain.join

let[@zoo.opaque] yield =
  Stdlib.Domain.cpu_relax

let[@zoo.opaque] self_index =
  Stdlib.Domain.self_index

let[@zoo.opaque] recommended_domain_count =
  Stdlib.Domain.recommended_domain_count
