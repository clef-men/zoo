type t

val create :
  unit -> t

type status = First | Already_notified

val notify :
  t -> status

val prepare :
  t -> unit

val cancel :
  t -> status

val commit :
  t -> unit
