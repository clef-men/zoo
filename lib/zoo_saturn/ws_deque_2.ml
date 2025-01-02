type 'a t =
  'a ref Ws_deque_1.t

let create =
  Ws_deque_1.create

let push t v =
  Ws_deque_1.push t (ref v)

let steal t =
  match Ws_deque_1.steal t with
  | None ->
      None
  | Some slot ->
      Some !slot

let pop t =
  match Ws_deque_1.pop t with
  | None ->
      None
  | Some slot ->
      Some !slot
