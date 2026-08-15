(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/treiber_stack.ml
*)

type 'a t =
  'a Glist.t Atomic.t

let create () =
  Atomic.make Glist.Nil

let rec push t v backoff =
  let old = Atomic.get t in
  let new_ = Glist.Cons (v, old) in
  if not @@ Atomic.compare_and_set t old new_ then
    push t v (Backoff.once backoff)
let push t v =
  push t v Backoff.default

let rec pop t backoff =
  match Atomic.get t with
  | Glist.Nil ->
      None
  | Cons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then
        Some v
      else
        pop t (Backoff.once backoff)
let pop t =
  pop t Backoff.default

let snapshot t =
  Atomic.get t
