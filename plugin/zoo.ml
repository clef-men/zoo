let ghost_state =
  "zoo.program_logic.ghost_state"

let ownership =
  "zoo.program_logic.ghost_state.ownership"
let ownership_inductive () =
  ownership
  |> Libnames.qualid_of_string
  |> Nametab.global_inductive
let ownership_constr () =
  Constr.mkIndU (ownership_inductive (), UVars.Instance.empty)

let _Discard =
  "zoo.program_logic.ghost_state.Discard"
let _Discard_ref =
  _Discard
  |> Constrexpr_.mk_ref_string

let solve_inG =
  "zoo.iris.base_logic.lib.base.solve_inG"
let solve_inG_tactic () =
  solve_inG
  |> Libnames.qualid_of_string
  |> Tacenv.locate_tactic

let solve_iris_typeclass =
  "zoo.plugin.solve_iris_typeclass"
let solve_iris_typeclass_tactic () =
  solve_iris_typeclass
  |> Libnames.qualid_of_string
  |> Tacenv.locate_tactic
