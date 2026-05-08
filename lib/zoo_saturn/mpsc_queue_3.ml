(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a Clist.t
  ; mutable back: 'a Clist.t [@atomic]
  }

let create () =
  { front= ClistOpen; back= ClistOpen }

let is_empty t =
  match t.front with
  | ClistClosed ->
      true
  | ClistCons _ ->
      false
  | ClistOpen ->
      match t.back with
      | ClistCons _ ->
          false
      | _ ->
          true

let push_front t v =
  match t.front with
  | ClistClosed ->
      true
  | _ as front ->
      t.front <- ClistCons (v, front) ;
      false

let rec push_back t v =
  match t.back with
  | ClistClosed ->
      true
  | _ as back ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.back] back (ClistCons (v, back)) then (
        false
      ) else (
        Domain.yield () ;
        push_back t v
      )

let pop t =
  match t.front with
  | ClistClosed ->
      None
  | ClistCons (v, front) ->
      t.front <- front ;
      Some v
  | ClistOpen ->
      match Atomic.Loc.exchange [%atomic.loc t.back] ClistOpen with
      | ClistOpen ->
          None
      | _ as back ->
          match Clist.rev_app back ClistOpen with
          | ClistCons (v, front) ->
              t.front <- front ;
              Some v
          | _ ->
              assert false

let close t =
  match Atomic.Loc.exchange [%atomic.loc t.back] ClistClosed with
  | ClistClosed ->
      true
  | _ as back ->
      t.front <- Clist.app t.front (Clist.rev_app back ClistClosed) ;
      false
