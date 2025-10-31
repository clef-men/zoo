[@@@zoo.ignore]

let for_ ctx beg end_ chunk fn =
  let sz = end_ - beg in
  let num_chunk = sz / chunk in
  let rest = sz mod chunk in
  let num_task = num_chunk + Bool.to_int (rest != 0) in
  let num_pending = Atomic.make num_task in
  for i = 0 to num_chunk - 1 do
    Pool.async ctx (fun ctx ->
      for k = i * chunk to i * chunk + chunk - 1 do
        fn ctx k
      done ;
      Atomic.decr num_pending
    )
  done ;
  if rest != 0 then
    Pool.async ctx (fun ctx ->
      for k = num_chunk * chunk to end_ - 1 do
        fn ctx k
      done ;
      Atomic.decr num_pending
    ) ;
  Pool.wait_until ctx (fun () -> Atomic.get num_pending == 0)

let rec for_2 ctx beg end_ chunk fn =
  if end_ - beg <= chunk then
    for i = beg to end_ - 1 do
      fn ctx i
    done
  else
    let mid = beg + (end_ - beg) / 2 in
    let left =
      Future.async ctx @@ fun ctx ->
        for_2 ctx beg mid chunk fn
    in
    for_2 ctx mid end_ chunk fn ;
    Future.wait ctx left

let divide ctx beg end_ fn =
  let num_dom = Pool.size ctx + 1 in
  let sz = end_ - beg in
  let chunk = sz / num_dom in
  let rest = sz mod num_dom in
  let num_task = num_dom + Bool.to_int (rest != 0) in
  let num_pending = Atomic.make num_task in
  for i = 0 to num_dom - 1 do
    Pool.async ctx (fun ctx ->
      fn ctx (i * chunk) chunk ;
      Atomic.decr num_pending
    )
  done ;
  if rest != 0 then
    Pool.async ctx (fun ctx ->
      fn ctx (num_dom * chunk) rest ;
      Atomic.decr num_pending
    ) ;
  Pool.wait_until ctx (fun () -> Atomic.get num_pending == 0)

let rec fold ctx op body acc beg end_ =
  if beg == end_ then
    acc
  else
    let acc = op acc (body ctx beg) in
    let beg = beg + 1 in
    fold ctx op body acc beg end_
let fold ctx beg end_ chunk op body zero =
  let sz = end_ - beg in
  let num_chunk = sz / chunk in
  let rest = sz mod chunk in
  let num_task = num_chunk + Bool.to_int (rest != 0) in
  let num_pending = Atomic.make num_task in
  let sums = Array.make num_task zero in
  for i = 0 to num_chunk - 1 do
    Pool.async ctx (fun ctx ->
      let sum = fold ctx op body zero (i * chunk) ((i + 1) * chunk) in
      Array.unsafe_set sums i sum ;
      Atomic.decr num_pending
    )
  done ;
  if rest != 0 then
    Pool.async ctx (fun ctx ->
      let sum = fold ctx op body zero (num_chunk * chunk) end_ in
      Array.unsafe_set sums num_chunk sum ;
      Atomic.decr num_pending
    ) ;
  Pool.wait_until ctx (fun () -> Atomic.get num_pending == 0) ;
  Array.foldl op zero sums

let rec find ctx beg end_ pred found =
  if beg != end_ && !found != None then (
    if pred ctx beg then
      found := Some beg
    else
      let beg = beg + 1 in
      find ctx beg end_ pred found
  )
let find ctx beg end_ chunk pred =
  let sz = end_ - beg in
  let num_chunk = sz / chunk in
  let rest = sz mod chunk in
  let num_task = num_chunk + Bool.to_int (rest != 0) in
  let num_pending = Atomic.make num_task in
  let found = ref None in
  for i = 0 to num_chunk - 1 do
    Pool.async ctx (fun ctx ->
      find ctx (i * chunk) ((i + 1) * chunk) pred found ;
      Atomic.decr num_pending
    )
  done ;
  if rest != 0 then
    Pool.async ctx (fun ctx ->
      find ctx (num_chunk * chunk) end_ pred found ;
      Atomic.decr num_pending
    ) ;
  Pool.wait_until ctx (fun () -> Atomic.get num_pending == 0) ;
  !found
