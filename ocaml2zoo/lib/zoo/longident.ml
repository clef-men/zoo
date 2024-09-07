include Ocaml_common.Longident

let rec head = function
  | Lident s ->
      Some s
  | Ldot (t, _) ->
      head t
  | Lapply (_, _) ->
      None

let last = function
  | Lident s ->
      Some s
  | Ldot (_, s) ->
      Some s
  | Lapply (_, _) ->
      None

let rec of_array arr len i t =
  if i = len then
    t
  else
    of_array arr len (i + 1) (Ldot (t, arr.(i)))
let of_array arr =
  of_array arr (Array.length arr) 1 (Lident arr.(0))

let rec to_string sep acc = function
  | Lident s ->
      Some (s ^ acc)
  | Ldot (t, s) ->
      to_string sep (sep ^ s ^ acc) t
  | Lapply _ ->
      None
let to_string sep = function
  | Lident s ->
      Some s
  | Ldot (t, s) ->
      to_string sep (sep ^ s) t
  | Lapply _ ->
      None

module Map =
  Map.Make (struct
    type nonrec t =
      t
    let compare =
      compare
  end)
