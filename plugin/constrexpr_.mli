open Constrexpr

val mk_ref :
  Libnames.qualid -> constr_expr
val mk_ref_string :
  string -> constr_expr

val mk_app :
  constr_expr -> constr_expr list -> constr_expr
