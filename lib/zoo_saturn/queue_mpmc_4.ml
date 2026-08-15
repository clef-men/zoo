(* Based on:
   https://github.com/pramalhe/ConcurrencyFreaks/blob/5b3b9fcd232ccb5417724fa154e948d0f26b6442/CPP/queues/array/FAAArrayQueue.hpp
*)

[@@@zoo.ignore]

type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable next: ('a, [`Null | `Node]) node [@atomic]
    ; queue: 'a Tqueue_mpmc_2.t
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Node]) node [@atomic]
  ; mutable back: ('a, [`Node]) node [@atomic]
  }

let[@zoo.opaque] queues_size =
  1024

let create () =
  let front =
    Node {
      next= Null;
      queue= Tqueue_mpmc_2.create queues_size;
    }
  in
  { front; back= front }

let is_empty t =
  let Node front_r = t.front in
  let proph = Zoo.proph () in
  Tqueue_mpmc_2.is_empty front_r.queue &&
  Zoo.resolve proph (front_r.next == Null)

let rec fix_back t back new_back backoff =
  let Node new_back_r = new_back in
  if new_back_r.next == Null
  && not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back
  then
    fix_back t t.back new_back (Backoff.once backoff)
let fix_back t back new_back =
  fix_back t back new_back Backoff.default
let rec push t (node : (_, [`Node]) node) v backoff =
  let Node node_r = node in
  match node_r.next with
  | Node _ as next ->
      push t next v backoff
  | Null ->
      if not @@ Tqueue_mpmc_2.push node_r.queue v then
        match node_r.next with
        | Node _ as next ->
            Atomic.Loc.compare_and_set [%atomic.loc t.back] node next |> ignore ;
            push t next v backoff
        | Null ->
            let (Node _ as new_back : (_, [`Node]) node) =
              Node {
                next= Null;
                queue= Tqueue_mpmc_2.make queues_size v;
              }
            in
            if Atomic.Loc.compare_and_set [%atomic.loc node_r.next] Null new_back then
              fix_back t node new_back
            else
              push t node v (Backoff.once backoff)
let push t v =
  push t t.back v Backoff.default

let rec pop_aux t front backoff =
  let Node front_r = front in
  match Tqueue_mpmc_2.pop front_r.queue with
  | Something v ->
      Some v
  | Nothing ->
      pop t (Backoff.once backoff)
  | Anything ->
      match front_r.next with
      | Null ->
          None
      | Node _ as next ->
          Atomic.Loc.compare_and_set [%atomic.loc t.front] front next |> ignore ;
          pop t backoff
and pop t backoff =
  let Node front_r as front = t.front in
  let proph = Zoo.proph () in
  if Tqueue_mpmc_2.is_empty front_r.queue then
    match Zoo.resolve_with front_r.next proph () with
    | Null ->
        None
    | Node _ ->
        pop_aux t front backoff
  else
    pop_aux t front backoff
let pop t =
  pop t Backoff.default
