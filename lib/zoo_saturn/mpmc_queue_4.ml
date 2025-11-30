(* Based on:
   https://github.com/pramalhe/ConcurrencyFreaks/blob/5b3b9fcd232ccb5417724fa154e948d0f26b6442/CPP/queues/array/FAAArrayQueue.hpp
*)

[@@@zoo.ignore]

type ('a, _) node =
  | Null :
    ('a, [> `Null]) node
  | Node :
    { mutable next: ('a, [`Null | `Node]) node [@atomic];
      queue: 'a Mpmc_fqueue_2.t;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Node]) node [@atomic];
    mutable back: ('a, [`Node]) node [@atomic];
  }

let[@zoo.opaque] queues_size =
  1024

let create () =
  let front =
    Node {
      next= Null;
      queue= Mpmc_fqueue_2.create queues_size;
    }
  in
  { front; back= front }

let is_empty t =
  let Node front_r = t.front in
  Mpmc_fqueue_2.is_empty front_r.queue && front_r.next == Null

let rec fix_back t back new_back =
  let Node new_back_r = new_back in
  if new_back_r.next == Null
  && not @@ Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back
  then (
    Domain.yield () ;
    fix_back t t.back new_back
  )
let rec push t (node : (_, [`Node]) node) v =
  let Node node_r = node in
  match node_r.next with
  | Node _ as next ->
      push t next v
  | Null ->
      if not @@ Mpmc_fqueue_2.push node_r.queue v then
        match node_r.next with
        | Node _ as next ->
            Atomic.Loc.compare_and_set [%atomic.loc t.back] node next |> ignore ;
            push t next v
        | Null ->
            let (Node _ as new_back : (_, [`Node]) node) =
              Node {
                next= Null;
                queue= Mpmc_fqueue_2.make queues_size v;
              }
            in
            if Atomic.Loc.compare_and_set [%atomic.loc node_r.next] Null new_back then (
              fix_back t node new_back
            ) else (
              Domain.yield () ;
              push t node v
            )
let push t v =
  push t t.back v

let rec pop_1 t (node : (_, [`Node]) node) =
  let Node node_r = node in
  let proph = Zoo.proph () in
  if Mpmc_fqueue_2.is_empty node_r.queue then
    match Zoo.resolve_with node_r.next proph () with
    | Null ->
        None
    | Node _ ->
        pop_2 t node
  else
    pop_2 t node
and pop_2 t (node : (_, [`Node]) node) =
  let Node node_r = node in
  match Mpmc_fqueue_2.pop node_r.queue with
  | Some _ as res ->
      res
  | None ->
      match node_r.next with
      | Null ->
          None
      | Node _ as next ->
          Atomic.Loc.compare_and_set [%atomic.loc t.front] node next |> ignore ;
          pop_1 t next
let pop t =
  pop_1 t t.front
