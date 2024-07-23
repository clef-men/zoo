let test1 () =
  assert (1 + 1 == 2)

let test2 b =
  if b then assert false else ()
