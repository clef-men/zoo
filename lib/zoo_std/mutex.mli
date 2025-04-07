type t =
  Stdlib.Mutex.t

val create :
  unit -> t

val lock :
  t -> unit
val unlock :
  t -> unit

val synchronize :
  t -> unit

val protect :
  t -> (unit -> 'a) -> 'a
