module type BASE = sig
  type t

  type context

  type 'a task =
    context -> 'a

  type 'a future

  val create :
    num_domains:int -> unit -> t

  val size :
    context -> int

  val run :
    t -> 'a task -> 'a

  val kill :
    t -> unit

  val async :
    context -> 'a task -> 'a future

  val wait :
    context -> 'a future -> 'a

  val for_ :
    context -> beg:int -> end_:int -> chunk:int -> (context -> int -> unit) -> unit

  val divide :
    context -> beg:int -> end_:int -> (context -> int -> int -> unit) -> unit
end

module type S = sig
  include BASE

  val for_ :
    context -> beg:int -> end_:int -> ?chunk:int -> (context -> int -> unit) -> unit
end
