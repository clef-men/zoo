type t

val create :
  int -> t

val reset :
  t -> unit

val next t :
  t -> int
