val init :
  unit -> unit

val bits :
  unit -> int

val int :
  int -> int
val int_in_range :
  int -> int -> int

module State : sig
  type t

  val create :
    unit -> t

  val bits :
    t -> int

  val int :
    t -> int -> int
  val int_in_range :
    t -> int -> int -> int
end

module Round : sig
  type t

  val create :
    int -> t

  val reset :
    t -> unit

  val next :
    t -> int
end
