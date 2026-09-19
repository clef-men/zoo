include module type of struct
  include Vernacinterp
end

val interp :
  state:Vernacstate.t -> Vernacexpr.vernac_control -> Vernacstate.t
