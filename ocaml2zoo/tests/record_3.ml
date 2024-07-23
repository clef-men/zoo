type[@zoo.force_record] t =
  { f1: int;
    f2: int;
  }

let test () =
  let t = { f1= 0; f2= 1 } in
  t.f1
