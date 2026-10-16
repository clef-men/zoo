let location =
  "zoo.language.location.location"
let location_qualid =
  location
  |> Libnames.qualid_of_string
let location_globref () =
  location_qualid
  |> Nametab.global

let prophet_id =
  "zoo.language.syntax.prophet_id"
let prophet_id_qualid =
  prophet_id
  |> Libnames.qualid_of_string
let prophet_id_globref () =
  prophet_id_qualid
  |> Nametab.global

let val_ =
  "zoo.language.syntax.val"
let val_qualid =
  val_
  |> Libnames.qualid_of_string
let val_ref =
  val_
  |> Constrexpr_.mk_ref_string

let _ValLoc =
  "zoo.language.syntax.ValLoc"
let _ValLoc_ref =
  _ValLoc
  |> Constrexpr_.mk_ref_string

let _ValProph =
  "zoo.language.syntax.ValProph"
let _ValProph_ref =
  _ValProph
  |> Constrexpr_.mk_ref_string

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
