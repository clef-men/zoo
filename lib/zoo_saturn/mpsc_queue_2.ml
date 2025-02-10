(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a list;
    mutable back: 'a list [@atomic];
  }

let create () =
  { front= []; back= [] }

let is_empty t =
  match t.front with
  | _ :: _ ->
      false
  | [] ->
      t.back == []

let push_front t v =
  t.front <- v :: t.front

let rec push_back t v =
  let back = t.back in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back (v :: back) then (
    Domain.yield () ;
    push_back t v
  )

let pop t =
  match t.front with
  | [] ->
      begin match Lst.rev @@ Atomic.Loc.exchange [%atomic.loc t.back] [] with
      | [] ->
          None
      | v :: front ->
          t.front <- front ;
          Some v
      end
  | v :: front ->
      t.front <- front ;
      Some v
