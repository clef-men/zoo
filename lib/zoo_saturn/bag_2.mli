type 'a t

type 'a producer

type 'a consumer

val create :
  unit -> 'a t

val create_producer :
  'a t -> 'a producer

val create_consumer :
  'a t -> 'a consumer

val push :
  'a producer -> 'a -> unit

val pop :
  'a t -> 'a consumer -> 'a option
