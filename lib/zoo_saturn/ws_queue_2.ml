(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/ws_deque.ml
*)

type 'a t =
  'a ref Ws_queue_1.t

let create =
  Ws_queue_1.create

let push t v =
  Ws_queue_1.push t (ref v)

let steal t =
  match Ws_queue_1.steal t with
  | None ->
      None
  | Some slot ->
      Some !slot

let pop t =
  match Ws_queue_1.pop t with
  | None ->
      None
  | Some slot ->
      Some !slot
