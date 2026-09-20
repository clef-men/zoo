type 'a state =
  | Null
  | Offer of 'a [@generative]
  | Accept of 'a [@generative]

type 'a t =
  'a state Atomic.t

let create () =
  Atomic.make Null

let rec exchange t v =
  match Atomic.get t with
  | Null ->
      exchange_aux t v
  | Offer w as state ->
      if Atomic.compare_and_set t state (Accept v) then
        Some w
      else
        None
  | Accept _ ->
      None
and exchange_aux t v =
  if Atomic.compare_and_set t Null (Offer v) then (
    Domain.yield () ;
    match Atomic.exchange t Null with
    | Null ->
        assert false
    | Offer _ ->
        None
    | Accept w ->
        Some w
  ) else (
    exchange t v
  )
