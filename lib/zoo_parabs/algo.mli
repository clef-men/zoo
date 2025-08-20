[@@@zoo.ignore]

val for_ :
  Pool.context -> int -> int -> int -> (Pool.context -> int -> unit) -> unit

val divide :
  Pool.context -> int -> int -> (Pool.context -> int -> int -> unit) -> unit
