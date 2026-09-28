include module type of struct
  include Vernacinterp
end

val interp :
  state:Vernacstate.t ->
  (Libobject.locality option * Vernacexpr.synpure_vernac_expr) list ->
  Vernacstate.t
