type t

val create :
  int -> t

val notify :
  t -> unit
val notify_all :
  t -> unit

val prepare_wait :
  t -> int -> unit
val cancel_wait :
  t -> int -> unit
val commit_wait :
  t -> int -> unit
