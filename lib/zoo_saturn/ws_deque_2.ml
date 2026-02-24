(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/ws_deque.ml
*)

type 'a t =
  'a ref Ws_deque_1.t

let create =
  Ws_deque_1.create

let size =
  Ws_deque_1.size

let is_empty =
  Ws_deque_1.is_empty

let push t v =
  Ws_deque_1.push t (ref v)

let steal t =
  match Ws_deque_1.steal t with
  | None ->
      None
  | Some slot ->
      let v = !slot in
      slot := Obj.magic () ;
      Some v

let pop t =
  match Ws_deque_1.pop t with
  | None ->
      None
  | Some slot ->
      let v = !slot in
      slot := Obj.magic () ;
      Some v
