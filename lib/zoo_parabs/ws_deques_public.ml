type 'a t =
  'a Inf_ws_deque_2.t array

let create sz =
  Array.unsafe_init sz Inf_ws_deque_2.create

let size =
  Array.size

let push t i v =
  let deque = Array.unsafe_get t i in
  Inf_ws_deque_2.push deque v

let pop t i =
  let deque = Array.unsafe_get t i in
  Inf_ws_deque_2.pop deque

let steal_to t _i j =
  let deque = Array.unsafe_get t j in
  Inf_ws_deque_2.steal deque

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
