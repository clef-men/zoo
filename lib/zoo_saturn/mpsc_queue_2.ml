(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a Glst.t;
    mutable back: 'a Glst.t [@atomic];
  }

let create () =
  { front= Gnil; back= Gnil }

let is_empty t =
  match t.front with
  | Gcons _ ->
      false
  | Gnil ->
      t.back == Gnil

let push_front t v =
  t.front <- Gcons (v, t.front)

let rec push_back t v =
  let back = t.back in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back (Gcons (v, back)) then (
    Domain.yield () ;
    push_back t v
  )

let pop t =
  match t.front with
  | Gnil ->
      begin match Glst.rev @@ Atomic.Loc.exchange [%atomic.loc t.back] Gnil with
      | Gnil ->
          None
      | Gcons (v, front) ->
          t.front <- front ;
          Some v
      end
  | Gcons (v, front) ->
      t.front <- front ;
      Some v
