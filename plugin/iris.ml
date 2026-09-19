let gFunctors =
  "iris.base_logic.lib.iprop.gFunctors"
let gFunctors_ref =
  gFunctors
  |> Constrexpr_.mk_ref_string

let gFunctors_nil =
  "iris.base_logic.lib.iprop.gFunctors.nil"
let gFunctors_nil_ref =
  gFunctors_nil
  |> Constrexpr_.mk_ref_string

let gFunctors_app =
  "iris.base_logic.lib.iprop.gFunctors.app"
let gFunctors_app_ref =
  gFunctors_app
  |> Constrexpr_.mk_ref_string

let sigma =
  "Σ"
let sigma_ref =
  sigma
  |> Constrexpr_.mk_ref_string
let sigma_binder =
  sigma
  |> Names_.lname_of_string
  |> (fun name -> Constrexpr.CLocalAssum ([name], None, Default Explicit, gFunctors_ref))

let subG =
  "iris.base_logic.lib.iprop.subG"
let subG_ref =
  subG
  |> Constrexpr_.mk_ref_string
