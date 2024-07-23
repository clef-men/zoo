type t =
  { mutable f1: int;
    f2: int;
  }

let test () =
  let t1 = { f1= 0; f2= 1 } in
  let _ = t1.f1 in
  t1.f1 <- 0
