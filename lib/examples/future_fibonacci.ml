let rec main ctx n =
  if n <= 1 then
    n
  else
    let fut1 = Future.async ctx (fun ctx -> main ctx (n - 1)) in
    let fut2 = Future.async ctx (fun ctx -> main ctx (n - 2)) in
    Future.wait ctx fut1 + Future.wait ctx fut2

let main ~num_worker n =
  Pool.run ~num_worker (fun ctx -> main ctx n)
