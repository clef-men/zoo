let rec fibonacci n ctx =
  if n <= 1 then
    n
  else
    let fut1 = Pool.async ctx (fun ctx -> fibonacci (n - 1) ctx) in
    let fut2 = Pool.async ctx (fun ctx -> fibonacci (n - 2) ctx) in
    Pool.await ctx fut1 + Pool.await ctx fut2
let fibonacci n pool =
  Pool.run pool (fun ctx -> fibonacci n ctx)
