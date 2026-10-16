include module type of struct
  include Names
end

module Id : sig
  include module type of struct
    include Id
  end

  val map :
    (string -> string) -> t -> t
end

val lident_of_string :
  string -> lident

val lname_of_ident :
  Id.t -> lname
val lname_of_string :
  string -> lname
