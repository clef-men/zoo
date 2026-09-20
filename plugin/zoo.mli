open Ltac_plugin

val ghost_state :
  string

val solve_inG :
  string
val solve_inG_tactic :
  unit -> Tacexpr.ltac_constant
