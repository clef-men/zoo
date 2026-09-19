open Ltac_plugin

include module type of struct
  include Ltac_plugin.Tacenv
end

val locate_tactic :
  Libnames.qualid -> Tacexpr.ltac_constant
