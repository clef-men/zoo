type t =
  | A
  | B of int

let test () =
  let _ = A in
  let _ = B 0 in
  ()
