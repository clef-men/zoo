(* Based on:
   https://github.com/cameron314/concurrentqueue/blob/6dd38b8a1dbaa7863aa907045f32308a56a6ff5d/concurrentqueue.h
*)

type 'a producer =
  'a Spmc_queue.t

type 'a consumer =
  'a producer option ref

type 'a t =
  'a producer Mpmc_stack_1.t

let create =
  Mpmc_stack_1.create

let create_producer t =
  let producer = Spmc_queue.create () in
  Mpmc_stack_1.push t producer ;
  producer

let create_consumer _t =
  ref None

let push producer v =
  Spmc_queue.push producer v

let rec pop producers consumer =
  match producers with
  | [] ->
      None
  | producer :: producers ->
      match Spmc_queue.pop producer with
      | None ->
          pop producers consumer
      | Some _ as res ->
          consumer := Some producer ;
          res
let pop t consumer =
  pop (Mpmc_stack_1.snapshot t) consumer
let pop t consumer =
  match !consumer with
  | None ->
      pop t consumer
  | Some producer ->
      match Spmc_queue.pop producer with
      | None ->
          pop t consumer
      | Some _ as res ->
          res
