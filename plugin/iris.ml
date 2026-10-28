let gFunctors =
  "iris.base_logic.lib.iprop.gFunctors"
let gFunctors_constr =
  gFunctors
  |> Constrexpr_.mk_ref_string

let gFunctors_nil =
  "iris.base_logic.lib.iprop.gFunctors.nil"
let gFunctors_nil_constr =
  gFunctors_nil
  |> Constrexpr_.mk_ref_string

let gFunctors_app =
  "iris.base_logic.lib.iprop.gFunctors.app"
let gFunctors_app_constr =
  gFunctors_app
  |> Constrexpr_.mk_ref_string

let _Sigma =
  "Σ"
let _Sigma_constr =
  _Sigma
  |> Constrexpr_.mk_ref_string
let _Sigma_binder =
  _Sigma
  |> Names_.lname_of_string
  |> (fun name -> Constrexpr.CLocalAssum ([name], None, Default Explicit, gFunctors_constr))

let subG =
  "iris.base_logic.lib.iprop.subG"
let subG_constr =
  subG
  |> Constrexpr_.mk_ref_string

let _Timeless =
  "iris.bi.derived_connectives.Timeless"
let _Timeless_constr =
  _Timeless
  |> Constrexpr_.mk_ref_string

let _Persistent =
  "iris.bi.derived_connectives.Persistent"
let _Persistent_constr =
  _Persistent
  |> Constrexpr_.mk_ref_string

let dfrac =
  "iris.algebra.dfrac.dfrac"
let dfrac_inductive () =
  dfrac
  |> Libnames.qualid_of_string
  |> Nametab.global_inductive
let dfrac_constr () =
  Constr.mkIndU (dfrac_inductive (), UVars.Instance.empty)

let _DfracDiscarded =
  "iris.algebra.dfrac.DfracDiscarded"
let _DfracDiscarded_constr =
  _DfracDiscarded
  |> Constrexpr_.mk_ref_string

let gamma =
  "γ"
let gamma_lident =
  gamma
  |> Names_.lident_of_string
let gamma_lname =
  gamma
  |> Names_.lname_of_string
let gamma_constr =
  gamma
  |> Constrexpr_.mk_ref_string
