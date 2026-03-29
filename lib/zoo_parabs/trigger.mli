type t

val create :
  (unit -> bool) -> t

val probe :
  t -> bool

val notify_weak :
  t -> bool
val notify :
  t -> unit

val wait :
  t -> bool
