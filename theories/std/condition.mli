type t

val create :
  unit -> t

val wait :
  t -> Mutex.t -> unit

val notify :
  t -> unit
val notify_all :
  t -> unit

val wait_until :
  t -> Mutex.t -> (unit -> bool) -> unit
val wait_while :
  t -> Mutex.t -> (unit -> bool) -> unit
