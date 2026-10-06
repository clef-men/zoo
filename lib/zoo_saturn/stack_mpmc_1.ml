(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/treiber_stack.ml
*)

type 'a t =
  'a Glist.t Atomic.t

let create () =
  Atomic.make Glist.Nil

let try_push t v =
  let old = Atomic.get t in
  let new_ = Glist.Cons (v, old) in
  Atomic.compare_and_set t old new_

let rec push t v backoff =
  if not @@ try_push t v then
    push t v (Backoff.once backoff)
let push t v =
  push t v Backoff.default

let try_pop t =
  match Atomic.get t with
  | Glist.Nil ->
      Optional.Nothing
  | Cons (v, new_) as old ->
      if Atomic.compare_and_set t old new_ then
        Something v
      else
        Anything

let rec pop t backoff =
  match try_pop t with
  | Optional.Nothing ->
      None
  | Something v ->
      Some v
  | Anything ->
      pop t (Backoff.once backoff)
let pop t =
  pop t Backoff.default

let snapshot t =
  Atomic.get t
