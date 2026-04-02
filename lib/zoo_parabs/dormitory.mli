type t

val create :
  unit -> t

val push :
  t -> Sleeper.t -> unit

val wakeup_one :
  t -> unit

val wakeup_all :
  t -> unit
