type t

val create :
  unit -> t

val bits :
  t -> int

val int :
  t -> int -> int
val int_in_range :
  t -> int -> int -> int
