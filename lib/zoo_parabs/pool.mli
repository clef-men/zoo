type t

type context

type 'a task =
  context -> 'a

type 'a future

val create :
  int -> t

val run :
  t -> 'a task -> 'a

val kill :
  t -> unit

val size :
  context -> int

val async_silent :
  context -> unit task -> unit
val async :
  context -> 'a task -> 'a future

val wait_until :
  context -> (unit -> bool) -> unit
val wait_while :
  context -> (unit -> bool) -> unit

val wait :
  context -> 'a future -> 'a

val iter :
  context -> 'a future -> ('a -> unit) task -> unit

val map :
  context -> 'a future -> ('a -> 'b) task -> 'b future
