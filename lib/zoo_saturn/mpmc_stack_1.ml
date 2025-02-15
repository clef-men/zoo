(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/treiber_stack.ml
*)

type 'a t =
  'a Glst.t Atomic.t

let create () =
  Atomic.make Glst.Gnil

let rec push t v =
  let old = Atomic.get t in
  let new_ = Glst.Gcons (v, old) in
  if not @@ Atomic.compare_and_set t old new_ then (
    Domain.yield () ;
    push t v
  )

let rec pop t =
  match Atomic.get t with
  | Glst.Gnil ->
      None
  | Gcons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then (
        Some v
      ) else (
        Domain.yield () ;
        pop t
      )

let snapshot t =
  Atomic.get t
