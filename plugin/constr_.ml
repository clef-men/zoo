include Constr

let rec parameters t =
  match kind t with
  | Prod (bdr, ty, t) ->
      (bdr.binder_name, ty) :: parameters t
  | _ ->
      []
