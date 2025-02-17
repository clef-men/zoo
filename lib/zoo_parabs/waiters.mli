type t

type waiter

val create :
  unit -> t

val notify :
  t -> unit
val notify_many :
  t -> int -> unit

val prepare_wait :
  t -> waiter
val cancel_wait :
  t -> waiter -> unit
val commit_wait :
  t -> waiter -> unit
