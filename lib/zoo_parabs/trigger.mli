type t = (unit, (unit -> unit) Pool.task) Ivar_3.t

val create :
  unit -> t

val notify :
  Pool.context -> t -> unit
