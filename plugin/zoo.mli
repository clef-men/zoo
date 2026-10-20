open Ltac_plugin

val location :
  string
val location_globref :
  unit -> Names.GlobRef.t

val prophet_identifier :
  string
val prophet_identifier_globref :
  unit -> Names.GlobRef.t

val val_ :
  string
val val_qualid :
  Libnames.qualid
val val_ref :
  Constrexpr.constr_expr

val _ValLoc :
  string
val _ValLoc_ref :
  Constrexpr.constr_expr

val _ValProph :
  string
val _ValProph_ref :
  Constrexpr.constr_expr

val _ToVal :
  string
val _ToVal_ref :
  Constrexpr.constr_expr

val ghost_state :
  string

val ownership :
  string
val ownership_constr :
  unit -> Constr.t

val _Discard :
  string
val _Discard_ref :
  Constrexpr.constr_expr

val solve_inG :
  string
val solve_inG_tactic :
  unit -> Tacexpr.ltac_constant

val solve_iris_typeclass :
  string
val solve_iris_typeclass_tactic :
  unit -> Tacexpr.ltac_constant
