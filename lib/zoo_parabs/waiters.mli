type t

val create :
  unit -> t

val push :
  t -> Waiter.t -> unit

val notify_one :
  t -> unit

val notify_all :
  t -> unit
