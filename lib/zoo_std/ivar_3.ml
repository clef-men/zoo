type 'a waiter =
  'a -> unit

type 'a state =
  | Unset of 'a waiter list [@generative]
  | Set of 'a

type 'a t =
  'a state Atomic.t

let create () =
  Atomic.make (Unset [])

let is_set t =
  match Atomic.get t with
  | Unset _ ->
      false
  | Set _ ->
      true

let try_get t =
  match Atomic.get t with
  | Unset _ ->
      None
  | Set v ->
      Some v

let get t =
  match Atomic.get t with
  | Unset _ ->
      assert false
  | Set v ->
      v

let rec wait t waiter =
  match Atomic.get t with
  | Unset waiters ->
      if Atomic.compare_and_set t (Unset waiters) (Unset (waiter :: waiters)) then
        None
      else
        wait t waiter
  | Set v ->
      Some v

let set t v =
  match Atomic.exchange t (Set v) with
  | Set _ ->
      assert false
  | Unset waiters ->
      waiters
