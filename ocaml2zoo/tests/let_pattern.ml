let test1 () =
  let (x, y) = (0, 1) in
  x + y

let test2 () =
  let[@warning "-8"] Some i = Some 0 in
  i
