type 'a t =
  'a ref Ws_bqueue_1.t

let create =
  Ws_bqueue_1.create

let capacity =
  Ws_bqueue_1.capacity

let size =
  Ws_bqueue_1.size

let is_empty =
  Ws_bqueue_1.is_empty

let push t v =
  Ws_bqueue_1.push t (ref v)

let steal t =
  match Ws_bqueue_1.steal t with
  | None ->
      None
  | Some slot ->
      Some !slot

let pop t =
  match Ws_bqueue_1.pop t with
  | None ->
      None
  | Some slot ->
      Some !slot
