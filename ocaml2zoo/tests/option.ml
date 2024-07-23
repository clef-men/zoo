let test1 () =
  let _ = None in
  let _ = Some 0 in
  ()

let test2 o =
  match o with
  | None ->
      0
  | Some i ->
      i
