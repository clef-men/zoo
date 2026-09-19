let _ZooG =
  "zoo.program_logic.ghost_state.ZooG"
let _ZooG_ref =
  _ZooG
  |> Constrexpr_.mk_ref_string
let _ZooG_sigma =
  _ZooG_ref
  |> Constrexpr.(fun expr -> CApp (expr, [Iris.sigma_ref, None]))
  |> CAst.make

let zoo_G =
  "zoo۰G"
let zoo_G_binder =
  zoo_G
  |> Names_.lname_of_string
  |> (fun name -> Constrexpr.CLocalAssum ([name], None, Generalized (MaxImplicit, false), _ZooG_sigma))

let solve_inG =
  "zoo.iris.base_logic.lib.base.solve_inG"
let solve_inG_tactic () =
  solve_inG
  |> Libnames.qualid_of_string
  |> Tacenv.locate_tactic
