module Error : sig
  type t

  val pp :
    Format.formatter -> t -> unit
end

exception Error of Location.t * Error.t

val structure :
  string -> Typedtree.structure -> Syntax.structure
