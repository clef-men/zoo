(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a Clist.t
  ; mutable back: 'a Clist.t [@atomic]
  }

let create () =
  { front= Open; back= Open }

let is_empty t =
  match t.front with
  | Closed ->
      true
  | Cons _ ->
      false
  | Open ->
      match t.back with
      | Cons _ ->
          false
      | _ ->
          true

let push_front t v =
  match t.front with
  | Closed ->
      true
  | _ as front ->
      t.front <- Cons (v, front) ;
      false

let rec push_back t v =
  match t.back with
  | Closed ->
      true
  | _ as back ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.back] back (Cons (v, back)) then (
        false
      ) else (
        Domain.yield () ;
        push_back t v
      )

let pop t =
  match t.front with
  | Closed ->
      None
  | Cons (v, front) ->
      t.front <- front ;
      Some v
  | Open ->
      match Atomic.Loc.exchange [%atomic.loc t.back] Open with
      | Open ->
          None
      | _ as back ->
          match Clist.rev_app back Open with
          | Cons (v, front) ->
              t.front <- front ;
              Some v
          | _ ->
              assert false

let close t =
  match Atomic.Loc.exchange [%atomic.loc t.back] Closed with
  | Closed ->
      true
  | _ as back ->
      t.front <- Clist.app t.front (Clist.rev_app back Closed) ;
      false
