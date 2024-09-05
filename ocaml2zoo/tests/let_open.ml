let test1 () =
  let open Obj in
  field (new_block 0 1) 0

let test2 () =
  Obj.(field (new_block 0 1) 0)
