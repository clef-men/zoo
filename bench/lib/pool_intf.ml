module type BASE = sig
  type t

  type context

  type 'a task =
    context -> 'a

  val create :
    num_domain:int -> unit -> t

  val size :
    context -> int

  val run :
    t -> 'a task -> 'a

  val kill :
    t -> unit

  type 'a future

  val async :
    context -> 'a task -> 'a future

  val wait :
    context -> 'a future -> 'a
end

module type S = sig
  include BASE

  val for_ :
    beg:int -> end_:int -> ?chunk:int -> context -> (int -> int -> unit) task -> unit

  val for_each :
    beg:int -> end_:int -> ?chunk:int -> context -> (int -> unit) task -> unit
end
