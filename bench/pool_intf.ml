module type S = sig
  type t

  type context

  type 'a task =
    context -> 'a

  type 'a future

  val create :
    int -> t

  val run :
    t -> 'a task -> 'a

  val kill :
    t -> unit

  val async :
    context -> 'a task -> 'a future

  val wait :
    context -> 'a future -> 'a
end
