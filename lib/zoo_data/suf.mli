type element

type t

val create :
  unit -> t

val make :
  t -> element

val repr :
  t -> element -> element

val equiv :
  t -> element -> element -> bool

val union :
  t -> element -> element -> unit

type snapshot

val capture :
  t -> snapshot

val restore :
  t -> snapshot -> unit
