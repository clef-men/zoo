type t

val create :
  int -> t

val size :
  t -> int

val get :
  t -> int -> int -> float
val set :
  t -> int -> int -> float -> unit

module Parallel
  (Pool : Pool.S)
: sig
  val fill :
    Pool.context -> t -> float -> unit

  val copy :
    Pool.context -> t -> t

  val apply :
    Pool.context -> t -> (int -> int -> float) -> unit
end
