(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/ws_deque.ml
*)

type 'a t =
  'a ref Inf_ws_deque_1.t

let create =
  Inf_ws_deque_1.create

let push t v =
  Inf_ws_deque_1.push t (ref v)

let steal t =
  match Inf_ws_deque_1.steal t with
  | None ->
      None
  | Some slot ->
      Some !slot

let pop t =
  match Inf_ws_deque_1.pop t with
  | None ->
      None
  | Some slot ->
      Some !slot
