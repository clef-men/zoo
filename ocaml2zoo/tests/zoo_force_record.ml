type[@zoo.force_record] t1 =
  { f1: int;
    f2: int;
  }

let test1 () =
  let t = { f1= 0; f2= 1 } in
  t.f1

type t2 =
  | A
  | B of { f: int } [@zoo.force_record]

let test2 () =
  B { f= 0 }
