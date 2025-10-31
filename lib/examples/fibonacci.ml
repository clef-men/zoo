let rec fibonacci n ctx =
  if n <= 1 then
    n
  else
    let fut1 = Future.async ctx (fun ctx -> fibonacci (n - 1) ctx) in
    let fut2 = Future.async ctx (fun ctx -> fibonacci (n - 2) ctx) in
    Future.wait ctx fut1 + Future.wait ctx fut2
let fibonacci n pool =
  Pool.run pool (fun ctx -> fibonacci n ctx)
