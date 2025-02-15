(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/bounded_stack.ml
*)

type 'a lst =
  | Nil
  | Cons of int * 'a * 'a lst [@generative]

type 'a t =
  { capacity: int;
    mutable front: 'a lst [@atomic];
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

let rec push_aux t sz v front =
  let new_front = Cons (sz + 1, v, front) in
  if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
    true
  ) else (
    Domain.yield () ;
    push t v
  )
and push t v =
  match t.front with
  | Nil ->
      push_aux t 0 v Nil
  | Cons (sz, _, _) as front ->
      if t.capacity <= sz then
        false
      else
        push_aux t sz v front

let rec pop t =
  match t.front with
  | Nil ->
      None
  | Cons (_, v, new_front) as front ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] front new_front then (
        Some v
      ) else (
        Domain.yield () ;
        pop t
      )
