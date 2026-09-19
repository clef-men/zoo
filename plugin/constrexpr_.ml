open Constrexpr

let mk_ref id =
  CRef (id, None) |> CAst.make
let mk_ref_string str =
  str
  |> Libnames.qualid_of_string
  |> mk_ref

let mk_app expr exprs =
  let exprs = exprs |> List.map (fun arg -> arg, None) in
  CApp (expr, exprs) |> CAst.make
