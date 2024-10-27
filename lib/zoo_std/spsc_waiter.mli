type t

val create :
  unit -> t

val notify :
  t -> unit

val try_wait :
  t -> bool
val wait :
  t -> unit
