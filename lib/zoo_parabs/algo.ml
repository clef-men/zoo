[@@@zoo.ignore]

let for_ ctx beg end_ chunk fn =
  let sz = end_ - beg in
  let num_chunk = sz / chunk in
  let rest = sz mod chunk in
  let cnt = Atomic.make sz in
  for i = 0 to num_chunk - 1 do
    Pool.async_silent ctx (fun ctx ->
      for k = i * chunk to i * chunk + chunk - 1 do
        fn ctx k
      done ;
      Atomic.fetch_and_add cnt (- chunk) |> ignore
    )
  done ;
  if rest != 0 then
    Pool.async_silent ctx (fun ctx ->
      for k = num_chunk * chunk to end_ - 1 do
        fn ctx k
      done ;
      Atomic.fetch_and_add cnt (- rest) |> ignore
    ) ;
  Pool.wait_until ctx (fun () -> Atomic.get cnt == 0)
