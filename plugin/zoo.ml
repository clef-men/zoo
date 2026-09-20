let ghost_state =
  "zoo.program_logic.ghost_state"

let solve_inG =
  "zoo.iris.base_logic.lib.base.solve_inG"
let solve_inG_tactic () =
  solve_inG
  |> Libnames.qualid_of_string
  |> Tacenv.locate_tactic
