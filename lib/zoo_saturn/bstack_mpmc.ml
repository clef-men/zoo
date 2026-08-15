(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/bounded_stack.ml
*)

type 'a list =
  | Nil
  | Cons of int * 'a * 'a list [@generative]

type 'a t =
  { capacity: int
  ; mutable front: 'a list [@atomic]
  }

let create cap =
  { capacity= cap; front= Nil }

let size t =
  match t.front with
  | Nil ->
      0
  | Cons (sz, _, _) ->
      sz

let is_empty t =
  t.front == Nil

let rec push_aux t sz v front backoff =
  let new_front = Cons (sz + 1, v, front) in
  if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then
    true
  else
    push t v (Backoff.once backoff)
and push t v backoff =
  match t.front with
  | Nil ->
      push_aux t 0 v Nil backoff
  | Cons (sz, _, _) as front ->
      if t.capacity <= sz then
        false
      else
        push_aux t sz v front backoff
let push t v =
  push t v Backoff.default

let rec pop t backoff =
  match t.front with
  | Nil ->
      None
  | Cons (_, v, new_front) as front ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then
        Some v
      else
        pop t (Backoff.once backoff)
let pop t =
  pop t Backoff.default
