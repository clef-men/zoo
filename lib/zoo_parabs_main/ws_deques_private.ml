(* Based on:
   https://inria.hal.science/hal-00863028
*)

type status =
  | Blocked
  | Nonblocked

type request =
  | RequestBlocked
  | RequestNone
  | RequestSome of int

type 'a response =
  | ResponseWaiting
  | ResponseNone
  | ResponseSome of 'a

type 'a t =
  { size: int;
    queues: 'a Queue_3.t array;
    statuses: status array;
    requests: request Atomic_array.t;
    responses: 'a response array;
    mutable force_mutable: unit; (* for verification *)
  }

let create sz =
  { size= sz;
    queues= Array.unsafe_init sz Queue_3.create;
    statuses= Array.unsafe_make sz Nonblocked;
    requests= Atomic_array.make sz RequestNone;
    responses= Array.unsafe_make sz ResponseWaiting;
    force_mutable= ();
  }

let size t =
  t.size

let block t i =
  Array.unsafe_set t.statuses i Blocked ;
  match Atomic_array.unsafe_xchg t.requests i RequestBlocked with
  | RequestSome j ->
      Array.unsafe_set t.responses j ResponseNone
  | _ ->
      ()

let unblock t i =
  Atomic_array.unsafe_set t.requests i RequestNone ;
  Array.unsafe_set t.statuses i Nonblocked

let respond t i =
  match Atomic_array.unsafe_get t.requests i with
  | RequestSome j ->
      let response =
        match Queue_3.pop_front (Array.unsafe_get t.queues i) with
        | Some v ->
            ResponseSome v
        | _ ->
            ResponseNone
      in
      Array.unsafe_set t.responses j response ;
      Atomic_array.unsafe_set t.requests i RequestNone
  | _ ->
      ()

let push t i v =
  Queue_3.push (Array.unsafe_get t.queues i) v ;
  respond t i

let pop t i =
  let res = Queue_3.pop_back (Array.unsafe_get t.queues i) in
  respond t i ;
  res

let rec steal_to t i =
  match Array.unsafe_get t.responses i with
  | ResponseWaiting ->
      Domain.yield () ;
      steal_to t i
  | ResponseNone ->
      Array.unsafe_set t.responses i ResponseWaiting ;
      None
  | ResponseSome v ->
      Array.unsafe_set t.responses i ResponseWaiting ;
      Some v
let steal_to t i j =
  if Array.unsafe_get t.statuses j == Nonblocked
  && Atomic_array.unsafe_cas t.requests j RequestNone (RequestSome i)
  then
    steal_to t i
  else
    None

let rec steal_as t sz i round n =
  if n <= 0 then
    None
  else
    let j = (i + 1 + Random_round.next round) mod sz in
    match steal_to t i j with
    | None ->
        steal_as t sz i round (n - 1)
    | _ as res ->
        res
let steal_as t i round =
  let sz = size t in
  steal_as t sz i round (sz - 1)
