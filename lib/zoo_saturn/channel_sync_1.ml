type 'a state =
  | Null
  | Sender_offer of 'a [@generative]
  | Sender_accept of 'a [@generative]
  | Receiver_offer
  | Receiver_accept

type 'a t =
  'a state Atomic.t

let create () =
  Atomic.make Null

let rec send t v =
  match Atomic.get t with
  | Null ->
      send_aux t v
  | Receiver_offer ->
      Atomic.compare_and_set t Receiver_offer (Sender_accept v)
  | _ ->
      false
and send_aux t v =
  if Atomic.compare_and_set t Null (Sender_offer v) then (
    Domain.yield () ;
    match Atomic.exchange t Null with
    | Sender_offer _ ->
        false
    | Receiver_accept ->
        true
    | _ ->
        assert false
  ) else (
    send t v
  )

let rec recv t =
  match Atomic.get t with
  | Null ->
      recv_aux t
  | Sender_offer v as state ->
      if Atomic.compare_and_set t state Receiver_accept then
        Some v
      else
        None
  | _ ->
      None
and recv_aux t =
  if Atomic.compare_and_set t Null Receiver_offer then (
    Domain.yield () ;
    match Atomic.exchange t Null with
    | Receiver_offer ->
        None
    | Sender_accept v ->
        Some v
    | _ ->
        assert false
  ) else (
    recv t
  )
