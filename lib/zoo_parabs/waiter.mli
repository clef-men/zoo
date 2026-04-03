type t

type token

val create :
  unit -> t

val notify :
  t -> bool

val prepare_wait :
  t -> token
val cancel_wait :
  t -> unit
val commit_wait :
  t -> token -> unit
