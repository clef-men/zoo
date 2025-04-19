type t

val create :
  int -> t

val try_lock :
  t -> bool

val lock :
  t -> unit

val unlock :
  t -> unit
