let location =
  "zoo.language.location.location"
let location_qualid =
  location
  |> Libnames.qualid_of_string
let location_globref () =
  location_qualid
  |> Nametab.global

let prophet_identifier =
  "zoo.language.prophet_identifier.prophet_identifier"
let prophet_identifier_qualid =
  prophet_identifier
  |> Libnames.qualid_of_string
let prophet_identifier_globref () =
  prophet_identifier_qualid
  |> Nametab.global

let _Tag =
  Printf.sprintf "zoo.language.tag.Tag%i"
let _Tag_ref i =
  _Tag i
  |> Constrexpr_.mk_ref_string

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

let _ToVal =
  "zoo.language.notations.ToVal"
let _ToVal_ref =
  _ToVal
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

let in_type =
  "zoo.language.notations.in_type"
let in_type_ref =
  in_type
  |> Constrexpr_.mk_ref_string

module Custom_entry = struct
  let field =
    "zoo.language.notations.zoo_field"
  let field_qualid =
    field
    |> Libnames.qualid_of_string

  let proj =
    "zoo.language.notations.zoo_proj"
  let proj_qualid =
    proj
    |> Libnames.qualid_of_string

  let tag =
    "zoo.language.notations.zoo_tag"
  let tag_qualid =
    tag
    |> Libnames.qualid_of_string
end
