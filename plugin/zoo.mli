open Ltac_plugin

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
