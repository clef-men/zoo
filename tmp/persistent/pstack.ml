type 'a t =
  'a list

let empty =
  []

let is_empty =
  Lst.is_empty

let push t v =
  v :: t

let pop = function
  | [] ->
      None
  | v :: t ->
      Some (v, t)
