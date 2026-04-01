type t =
  { id : int
  ; mutex : Mutex.t
  ; condition : Condition.t
  ; mutable sleep_round : int
  ; mutable last_wakeup : int
  }
(* [id] is useful to write debugging prints.

   [sleep_round] and [last_wakeup] are protected by the mutex.
   [last_wakeup] is the round at which the last wakeup occurred:
   when [sleep_round = last_wakeup], the sleeper has been awoken
   after the last [prepare_sleep] call. *)

let create id =
  { id
  ; mutex = Mutex.create ()
  ; condition = Condition.create ()
  ; sleep_round = 0
  ; last_wakeup = 0
  }

let wakeup t =
  let wakeup =
    Mutex.protect t.mutex @@ fun () ->
    if t.last_wakeup = t.sleep_round then (
      false
    ) else (
      t.last_wakeup <- t.sleep_round;
      true
    )
  in
  (* We intentionally call Condition.notify after releasing the mutex
     so that the caller of Condition.wait can take it immediately; see
     https://en.cppreference.com/w/cpp/thread/condition_variable/notify_one.html
     https://stackoverflow.com/questions/17101922/do-i-have-to-acquire-lock-before-calling-condition-variable-notify-one/17102100#17102100

     This implies that the notification can race with
     a mutex-protected critical section in [cancel_sleep] or
     [commit_sleep] below. This is fine as they check the
     mutex-protected [last_wakeup] to tell if [wakeup] was called, and
     do the right thing in that case whether or not the notification
     is received. *)
  if wakeup then Condition.notify t.condition;
  wakeup

let prepare_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  t.sleep_round <- t.sleep_round + 1

type status = Wakeup_received | No_wakeup
let cancel_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  if t.last_wakeup = t.sleep_round then (
    (* We received a notification between [prepare] and [cancel]. *)
    Wakeup_received
  ) else (
    (* Update [last_wakeup] so that a future wakeup
       on this round is not counted as 'useful'. *)
    t.last_wakeup <- t.sleep_round;
    No_wakeup
  )

let commit_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  if t.sleep_round = t.last_wakeup then (
    (* we received a notification between [prepare] and [commit] *)
    ()
  ) else (
    Condition.wait t.condition t.mutex;
  )
