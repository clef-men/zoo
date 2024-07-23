include Ocaml_common.Path

let rec of_array arr len i t =
  if i = len then
    t
  else
    of_array arr len (i + 1) (Pdot (t, arr.(i)))
let of_array arr =
  of_array arr (Array.length arr) 1 (Pident (Ident.create_persistent arr.(0)))

let rec to_string' sep acc = function
  | Pident ident ->
      Some (Ident.name ident ^ acc)
  | Pdot (t, s) ->
      to_string' sep (sep ^ s ^ acc) t
  | Papply _ ->
      None
  | Pextra_ty (t, Pcstr_ty s) ->
      to_string' sep (sep ^ s ^ acc) t
  | Pextra_ty (t, Pext_ty) ->
      to_string' sep acc t
let rec to_string sep = function
  | Pident ident ->
      Some (Ident.name ident)
  | Pdot (t, s) ->
      to_string' sep (sep ^ s) t
  | Papply _ ->
      None
  | Pextra_ty (t, Pcstr_ty s) ->
      to_string' sep s t
  | Pextra_ty (t, Pext_ty) ->
      to_string sep t
