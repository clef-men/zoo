type t

type context

type 'a task =
  context -> 'a

val create :
  int -> t

val run :
  t -> 'a task -> 'a

val kill :
  t -> unit

val size :
  context -> int

val async :
  context -> unit task -> unit

val wait_until :
  context -> (unit -> bool) -> unit
val wait_while :
  context -> (unit -> bool) -> unit
