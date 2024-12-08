(* Based on:
   https://github.com/ocaml-multicore/picos/blob/07d6c2d391e076b490098c0379d01208b3a9cc96/test/lib/foundation/mpsc_queue.ml
*)

type 'a t =
  { mutable front: 'a list [@atomic];
    mutable back: 'a list [@atomic];
  }

let create () =
  { front= []; back= [] }

let rec push t v =
  let back = t.back in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back (v :: back) then (
    Domain.yield () ;
    push t v
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
