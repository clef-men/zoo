type t

val create :
  int -> t

(* [true] if wakeup is succesful, [false] if already awake. *)
val wakeup :
  t -> bool

val prepare_sleep :
  t -> unit

(* [true] if cancel was succesful,
   [false] if a notification received in the meantime. *)
val cancel_sleep :
  t -> bool

val commit_sleep :
  t -> unit
