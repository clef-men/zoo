type t

type context

type 'a task =
  context -> 'a

type 'a future

val create :
  int -> t

val run :
  t -> 'a task -> 'a

val silent_async :
  context -> unit task -> unit
val async :
  context -> 'a task -> 'a future

val wait_until :
  context -> (unit -> bool) -> unit
val wait_while :
  context -> (unit -> bool) -> unit

val await :
  context -> 'a future -> 'a

val kill :
  t -> unit
