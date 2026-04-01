type t

val create :
  int -> t

(* [true] if wakeup is succesful, [false] if already awake. *)
val wakeup :
  t -> bool

val prepare_sleep :
  t -> unit

type status = Wakeup_received | No_wakeup
val cancel_sleep :
  t -> status

val commit_sleep :
  t -> unit
