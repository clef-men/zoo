(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a Glist.t
  ; mutable back: 'a Glist.t [@atomic]
  }

let create () =
  { front= Nil; back= Nil }

let is_empty t =
  match t.front with
  | Cons _ ->
      false
  | Nil ->
      t.back == Nil

let push_front t v =
  t.front <- Cons (v, t.front)

let rec push_back t v =
  let back = t.back in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back (Cons (v, back)) then (
    Domain.yield () ;
    push_back t v
  )

let pop t =
  match t.front with
  | Nil ->
      begin match Glist.rev @@ Atomic.Loc.exchange [%atomic.loc t.back] Nil with
      | Nil ->
          None
      | Cons (v, front) ->
          t.front <- front ;
          Some v
      end
  | Cons (v, front) ->
      t.front <- front ;
      Some v
