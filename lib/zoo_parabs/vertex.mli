type t

val create :
  unit Pool.task -> t

val precede :
  t -> t -> unit

val release :
  Pool.context -> t -> unit
