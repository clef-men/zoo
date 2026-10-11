include module type of struct
  include Constr
end

val parameters :
  t -> (Names.Name.t * t) list
