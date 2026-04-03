type t =
  { mutex: Mutex.t
  ; condition: Condition.t
  ; mutable state : int [@atomic]
  }

type token =
  int

let status_shift =
  0
let status_bits =
  1
let status_mask =
  1 lsl status_bits - 1
let status_incr =
  1 lsl status_shift
let status_decr =
  - status_incr
let epoch_shift =
  status_bits
let epoch_incr =
  1 lsl epoch_shift

let[@inline] status state =
  state land status_mask
let[@inline] epoch state =
  state lsr epoch_shift

let create () =
  { mutex= Mutex.create ()
  ; condition= Condition.create ()
  ; state= 0
  }

let notify t =
  let state = Atomic.Loc.fetch_and_add [%atomic.loc t.state] epoch_incr in
  if 0 < status state then (
    Condition.notify t.condition ;
    true
  ) else (
    false
  )

let prepare_wait t =
  let state = Atomic.Loc.fetch_and_add [%atomic.loc t.state] status_incr in
  epoch state

let cancel_wait t =
  Atomic.Loc.fetch_and_add [%atomic.loc t.state] status_decr |> ignore

let commit_wait t token =
  Mutex.protect t.mutex (fun () ->
    Condition.wait_while t.condition t.mutex @@ fun () ->
      epoch t.state == token
  ) ;
  Atomic.Loc.fetch_and_add [%atomic.loc t.state] status_decr |> ignore
