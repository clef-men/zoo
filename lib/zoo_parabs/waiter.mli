type t

val create :
  unit -> t

val notify :
  t -> bool

val prepare_wait :
  t -> unit
val cancel_wait :
  t -> unit
val commit_wait :
  t -> unit
