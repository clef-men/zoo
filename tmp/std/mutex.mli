type t

val create :
  unit -> t

val lock :
  t -> unit
val unlock :
  t -> unit

val protect :
  t -> (unit -> unit) -> unit
