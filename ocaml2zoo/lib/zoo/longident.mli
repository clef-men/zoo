include module type of struct
  include Ocaml_common.Longident
end

val head :
  t -> string option

val last :
  t -> string option

val of_array :
  string array -> t

val to_string :
  string -> t -> string option

module Map :
  Map.S with type key = t
