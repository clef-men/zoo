(* Based on:
   https://github.com/cameron314/concurrentqueue/blob/6dd38b8a1dbaa7863aa907045f32308a56a6ff5d/concurrentqueue.h
*)

type 'a queue =
  'a Spmc_queue.t

type ('a, _) producers_ =
  | Null :
    ('a, [> `Null]) producers_
  | Node :
    { next: 'a producers;
      mutable queue: 'a queue option;
    } ->
    ('a, [> `Node]) producers_
and 'a producers =
  ('a, [`Null | `Node]) producers_
type 'a producer_node =
  ('a, [`Node]) producers_

type 'a producer =
  { producer_queue: 'a queue;
    producer_node: 'a producer_node;
  }

type 'a consumer =
  { mutable consumer_queue: 'a queue option;
  }

type 'a t =
  { mutable producers: 'a producers [@atomic];
  }

let create () =
  { producers= Null }

let rec add_producer t queue =
  let producers = t.producers in
  let (Node _ as new_producers : _ producer_node) = Node { next= producers; queue } in
  if Atomic.Loc.compare_and_set [%atomic.loc t.producers] producers new_producers then (
    new_producers
  ) else (
    Domain.yield () ;
    add_producer t queue
  )
let add_producer t queue =
  add_producer t (Some queue)
let create_producer t =
  let queue = Spmc_queue.create () in
  let node = add_producer t queue in
  { producer_queue= queue;
    producer_node= node;
  }

let close_producer producer =
  let Node node_r = producer.producer_node in
  node_r.queue <- None

let create_consumer _t =
  { consumer_queue= None }

let push producer v =
  Spmc_queue.push producer.producer_queue v

let rec pop consumer = function
  | Null ->
      None
  | Node node_r ->
      match node_r.queue with
      | None ->
          pop consumer node_r.next
      | Some queue ->
          match Spmc_queue.pop queue with
          | None ->
              pop consumer node_r.next
          | Some _ as res ->
              consumer.consumer_queue <- Some queue ;
              res
let pop t consumer =
  pop consumer t.producers
let pop t consumer =
  match consumer.consumer_queue with
  | None ->
      pop t consumer
  | Some queue ->
      match Spmc_queue.pop queue with
      | None ->
          pop t consumer
      | Some _ as res ->
          res
