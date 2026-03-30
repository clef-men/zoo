type t =
  { id : int
  ; mutex : Mutex.t
  ; condition : Condition.t
  ; mutable sleeping : bool
  ; mutable sleep_round : int
  ; mutable last_wakeup : int
  }
(* [id] is useful to write debugging prints.

   [sleeping], [sleep_round] and [last_wakeup] are protected by the mutex.
   [last_wakeup] is the round at which the last wakeup occurred:
   when [sleep_round = last_wakeup], the sleeper has been awoken
   after the last [prepare_sleep] call. *)

let create id =
  { id
  ; mutex = Mutex.create ()
  ; condition = Condition.create ()
  ; sleeping = false
  ; sleep_round = 0
  ; last_wakeup = 0
  }

let wakeup t =
  Mutex.protect t.mutex @@ fun () ->
  if t.last_wakeup = t.sleep_round then
    (* we already received a wakeup *)
    false
  else (
    (* even if we were not yet sleeping, the wakeup is 'useful' *)
    t.last_wakeup <- t.sleep_round;
    if t.sleeping then Condition.notify t.condition;
    true
  )

let prepare_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  t.sleep_round <- t.sleep_round + 1

let cancel_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  assert (not t.sleeping);
  let no_wakeup_received = t.last_wakeup < t.sleep_round in
  (* pretend we receive a wakeup so that a future wakeup
     on this round is not counted as 'useful' *)
  t.last_wakeup <- t.sleep_round;
  no_wakeup_received

let commit_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  assert (not t.sleeping);
  if t.sleep_round = t.last_wakeup then (
    (* we received a notification between [prepare] and [commit] *)
    ()
  ) else (
    t.sleeping <- true;
    Condition.wait t.condition t.mutex;
    t.sleeping <- false
  )
