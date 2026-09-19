open Ltac_plugin

val _ZooG :
  string
val _ZooG_ref :
  Constrexpr.constr_expr
val _ZooG_sigma :
  Constrexpr.constr_expr

val zoo_G :
  string
val zoo_G_binder :
  Constrexpr.local_binder_expr

val solve_inG :
  string
val solve_inG_tactic :
  unit -> Tacexpr.ltac_constant
