let main ~num_domain n =
  let pool = Pool.create ~num_domain in
  let cnt = Atomic.make 0 in
  Pool.run pool (fun ctx ->
    for _ = 0 to n - 1 do
      Pool.async ctx (fun _ctx -> Atomic.incr cnt)
    done
  ) ;
  Pool.close pool ;
  Atomic.get cnt
