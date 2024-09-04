let test1 b =
  if b then 0 else 1

let test2 b0 b1 =
  if b0 then 0 else if b1 then 1 else 2

let test3 b0 b1 b2 =
  if b0 then 0 else if b1 then 1 else if b2 then 2 else 3

let test4 b =
  if not b then 0 else 1
