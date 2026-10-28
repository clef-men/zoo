open Ltac_plugin

val location :
  string
val location_gref :
  unit -> Names.GlobRef.t

val prophet_identifier :
  string
val prophet_identifier_gref :
  unit -> Names.GlobRef.t

val _Tag :
  int -> string
val _Tag_constr :
  int -> Constrexpr.constr_expr

val val_ :
  string
val val_qualid :
  Libnames.qualid
val val_constr :
  Constrexpr.constr_expr

val _ValLoc :
  string
val _ValLoc_constr :
  Constrexpr.constr_expr

val _ValProph :
  string
val _ValProph_constr :
  Constrexpr.constr_expr

val _ToVal :
  string
val _ToVal_constr :
  Constrexpr.constr_expr

val ghost_state :
  string

val ownership :
  string
val ownership_constr :
  unit -> Constr.t

val _Discard :
  string
val _Discard_constr :
  Constrexpr.constr_expr

val solve_inG :
  string
val solve_inG_tactic :
  unit -> Tacexpr.ltac_constant

val solve_iris_typeclass :
  string
val solve_iris_typeclass_tactic :
  unit -> Tacexpr.ltac_constant

val in_type :
  string
val in_type_constr :
  Constrexpr.constr_expr

module Custom_entry : sig
  val constructor :
    string
  val constructor_qualid :
    Libnames.qualid

  val field :
    string
  val field_qualid :
    Libnames.qualid

  val projection :
    string
  val projection_qualid :
    Libnames.qualid
end
