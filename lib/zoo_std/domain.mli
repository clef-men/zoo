type !'a t

val spawn :
  (unit -> 'a) -> 'a t

val join :
  'a t -> 'a

val yield :
  unit -> unit

val self_index  :
  unit -> int

val recommended_domain_count  :
  unit -> int
