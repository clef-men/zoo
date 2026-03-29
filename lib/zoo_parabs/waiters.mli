type t

val create :
  unit -> t

val notify :
  t -> int -> unit
val notify_all :
  t -> unit

val push :
  t -> Trigger.t -> unit

val prepare_wait :
  t -> Trigger.t
val cancel_wait :
  t -> Trigger.t -> int -> unit
val commit_wait :
  t -> Trigger.t -> unit
