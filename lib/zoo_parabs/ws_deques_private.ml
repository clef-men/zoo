(* Based on:
   https://inria.hal.science/hal-00863028
*)

type request =
  | Blocked
  | No_request
  | Request of int

type 'a response =
  | No_response
  | No
  | Yes of 'a

type 'a t =
  { deques: 'a Deque.t array;
    flags: bool array;
    requests: request Atomic_array.t;
    responses: 'a response array;
  }

let create sz =
  { deques= Array.unsafe_init sz Deque.create;
    flags= Array.unsafe_make sz false;
    requests= Atomic_array.make sz Blocked;
    responses= Array.unsafe_make sz No_response;
  }

let size t =
  Array.size t.deques

let block t i j =
  Array.unsafe_set t.responses j No ;
  Atomic_array.unsafe_set t.requests i Blocked
let block t i =
  Array.unsafe_set t.flags  i false ;
  let requests = t.requests in
  match Atomic_array.unsafe_get requests i with
  | Blocked ->
      ()
  | No_request ->
      if not @@ Atomic_array.unsafe_cas requests i No_request Blocked then
        begin match Atomic_array.unsafe_get requests i with
        | Request j ->
            block t i j
        | _ ->
            assert false
        end
  | Request j ->
      block t i j

let unblock t i =
  Atomic_array.unsafe_set t.requests i No_request ;
  Array.unsafe_set t.flags i true

let respond t i =
  let deque = Array.unsafe_get t.deques i in
  let requests = t.requests in
  match Atomic_array.unsafe_get requests i with
  | Request j ->
      let v =
        match Deque.pop_front deque with
        | Some v ->
            v
        | _ ->
            assert false
      in
      Array.unsafe_set t.responses j (Yes v) ;
      Atomic_array.unsafe_set requests i (if Deque.is_empty deque then Blocked else No_request)
  | _ ->
      ()

let push t i v =
  let deque = Array.unsafe_get t.deques i in
  Deque.push_back deque v ;
  if Array.unsafe_get t.flags i then
    respond t i
  else
    unblock t i

let pop t i =
  let deque = Array.unsafe_get t.deques i in
  let res = Deque.pop_back deque in
  begin match res with
  | None ->
      ()
  | Some _ ->
      if Deque.is_empty deque then
        block t i
      else
        respond t i
  end ;
  res

let rec steal_to t i =
  match Array.unsafe_get t.responses i with
  | No_response ->
      Domain.yield () ;
      steal_to t i
  | No ->
      None
  | Yes v ->
      Array.unsafe_set t.responses i No_response ;
      Some v
let steal_to t i j =
  if Array.unsafe_get t.flags j
  && Atomic_array.unsafe_cas t.requests j No_request (Request i) then
    steal_to t i
  else
    None

let rec steal_as t sz i round n =
  if n <= 0 then (
    None
  ) else (
    let j = (i + 1 + Random_round.next round) mod sz in
    match steal_to t i j with
    | None ->
        steal_as t sz i round (n - 1)
    | _ as res ->
        res
  )
let steal_as t i round =
  let sz = size t in
  steal_as t sz i round (sz - 1)
