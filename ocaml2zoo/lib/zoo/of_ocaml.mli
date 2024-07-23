module Error : sig
  type t

  val to_string :
    t -> string
  val pp :
    Format.formatter -> t -> unit
end

exception Unsupported of Location.t * Error.t

val structure :
  string -> Typedtree.structure -> Syntax.structure
