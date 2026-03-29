type 'a t =
  'a Ws_deque_2.t array

let create sz =
  Array.unsafe_init sz Ws_deque_2.create

let size =
  Array.size

let block _t _i =
  ()

let unblock _t _i =
  ()

let push t i v =
  let queue = Array.unsafe_get t i in
  Ws_deque_2.push queue v

let pop t i =
  let queue = Array.unsafe_get t i in
  Ws_deque_2.pop queue

let steal_to t _i j =
  let queue = Array.unsafe_get t j in
  Ws_deque_2.steal queue

let rec steal_as t sz i round n =
  if n <= 0 then (
    None
  ) else (
    let j = (i + 1 + Random_round.next round) mod sz in
    match steal_to t i j with
    | None ->
        steal_as t sz i round (n - 1)
    | _ as res ->
        res
  )
let steal_as t i round =
  let sz = size t in
  steal_as t sz i round (sz - 1)
