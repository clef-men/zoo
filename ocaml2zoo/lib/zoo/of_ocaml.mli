module Error : sig
  type t

  val pp :
    t Fmt.t
end

exception Error of Location.t * Error.t

val structure :
  string -> Typedtree.structure -> Syntax.structure
