(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a Clst.t [@atomic];
    mutable back: 'a Clst.t [@atomic];
  }

let create () =
  { front= ClstOpen; back= ClstOpen }

let push_front t v =
  match t.front with
  | ClstClosed ->
      true
  | _ as front ->
      t.front <- ClstCons (v, front) ;
      false

let rec push_back t v =
  match t.back with
  | ClstClosed ->
      true
  | _ as back ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.back] back (ClstCons (v, back)) then (
        false
      ) else (
        Domain.yield () ;
        push_back t v
      )

let pop_front t =
  match t.front with
  | ClstClosed ->
      None
  | ClstCons (v, front) ->
      t.front <- front ;
      Some v
  | ClstOpen ->
      match Atomic.Loc.exchange [%atomic.loc t.back] ClstOpen with
      | ClstOpen ->
          None
      | _ as back ->
          match Clst.rev_app back ClstOpen with
          | ClstCons (v, front) ->
              t.front <- front ;
              Some v
          | _ ->
              assert false

let close t =
  match Atomic.Loc.exchange [%atomic.loc t.back] ClstClosed with
  | ClstClosed ->
      true
  | _ as back ->
      t.front <- Clst.app t.front (Clst.rev_app back ClstClosed) ;
      false

let is_empty t =
  match t.front with
  | ClstClosed ->
      true
  | ClstCons _ ->
      false
  | ClstOpen ->
      match t.back with
      | ClstCons _ ->
          false
      | _ ->
          true
