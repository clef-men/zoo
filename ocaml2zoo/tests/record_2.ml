type t =
  { f1: int;
    f2: int;
  }

let test1 () =
  let t2 = { f1= 0; f2= 1 } in
  t2.f1

let test2 t =
  let { f1; f2 } = t in
  f1 + f2
