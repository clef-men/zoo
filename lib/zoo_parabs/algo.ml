[@@@zoo.ignore]

let adjust_chunk ctx beg end_ chunk =
  match chunk with
  | Some chunk ->
      chunk
  | None ->
      let num_dom = Pool.size ctx + 1 in
      let num_task = end_ - beg in
      if num_dom == 1 then
        num_task
      else
        Int.max 1 (num_task / (8 * num_dom))

let rec for_ ctx beg end_ chunk task =
  let num_task = end_ - beg in
  if num_task <= chunk then
    task ctx beg num_task
  else
    let mid = beg + num_task / 2 in
    let left =
      Future.async ctx @@ fun ctx ->
        for_ ctx beg mid chunk task
    in
    for_ ctx mid end_ chunk task ;
    Future.wait ctx left
let for_ ctx beg end_ chunk task =
  let chunk = adjust_chunk ctx beg end_ chunk in
  for_ ctx beg end_ chunk task

let for_each ctx beg end_ chunk task =
  for_ ctx beg end_ chunk @@ fun ctx beg sz ->
    for i = beg to beg + sz - 1 do
      task ctx i
    done

let rec fold_seq ctx beg end_ body op acc =
  if beg == end_ then
    acc
  else
    let acc = op acc (body ctx beg) in
    let beg = beg + 1 in
    fold_seq ctx beg end_ body op acc
let rec fold ctx beg end_ chunk body op zero =
  let num_task = end_ - beg in
  if num_task <= chunk then
    fold_seq ctx beg (beg + num_task) body op zero
  else
    let mid = beg + num_task / 2 in
    let left =
      Future.async ctx @@ fun ctx ->
        fold ctx beg mid chunk body op zero
    in
    let right = fold ctx mid end_ chunk body op zero in
    let left = Future.wait ctx left in
    op left right
let fold ctx beg end_ chunk body op zero =
  let chunk = adjust_chunk ctx beg end_ chunk in
  fold ctx beg end_ chunk body op zero

let rec find_seq ctx beg end_ pred found =
  if beg != end_ && Atomic.get found == None then (
    if pred ctx beg then
      Atomic.set found (Some beg)
    else
      let beg = beg + 1 in
      find_seq ctx beg end_ pred found
  )
let rec find ctx beg end_ chunk pred found =
  let num_task = end_ - beg in
  if num_task <= chunk then
    find_seq ctx beg (beg + num_task) pred found
  else if Atomic.get found == None then
    let mid = beg + num_task / 2 in
    let left =
      Future.async ctx @@ fun ctx ->
        find ctx beg mid chunk pred found
    in
    find ctx mid end_ chunk pred found ;
    Future.wait ctx left
let find ctx beg end_ chunk pred =
  let chunk = adjust_chunk ctx beg end_ chunk in
  let found = Atomic.make None in
  find ctx beg end_ chunk pred found ;
  Atomic.get found
