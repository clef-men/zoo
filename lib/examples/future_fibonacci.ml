let rec main ctx n =
  if n <= 1 then
    n
  else
    let fut1 = Future.async ctx (fun ctx -> main ctx (n - 1)) in
    let fut2 = Future.async ctx (fun ctx -> main ctx (n - 2)) in
    Future.wait ctx fut1 + Future.wait ctx fut2

let main ~num_domain n =
  Pool.run ~num_domain (fun ctx -> main ctx n)
