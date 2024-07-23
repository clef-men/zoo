type t =
  { f1: int;
    f2: int;
  }

let test () =
  let t2 = { f1= 0; f2= 1 } in
  t2.f1
