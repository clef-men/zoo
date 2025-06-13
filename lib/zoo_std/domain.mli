[@@@zoo.ignore]

type !'a t

type 'a key

val spawn :
  (unit -> 'a) -> 'a t

val join :
  'a t -> 'a

val local_new :
  (unit -> 'a) -> 'a key

val local_get :
  'a key -> 'a

val local_set :
  'a key -> 'a -> unit

val yield :
  unit -> unit

val self_index  :
  unit -> int

val recommended_domain_count  :
  unit -> int
