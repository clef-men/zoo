let main ~num_domain n =
  let cnt = Atomic.make 0 in
  Pool.run ~num_domain (fun ctx ->
    for _ = 0 to n - 1 do
      Pool.async ctx (fun _ctx -> Atomic.incr cnt)
    done
  ) ;
  Atomic.get cnt
