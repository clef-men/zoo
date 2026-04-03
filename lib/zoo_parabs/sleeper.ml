type t =
  { id : int
  ; mutex : Mutex.t
  ; condition : Condition.t
  ; mutable cancelled : bool;
  }
(* [id] is useful to write debugging prints.

   [cancelled] is protected by the mutex. *)

let create id =
  { id
  ; mutex = Mutex.create ()
  ; condition = Condition.create ()
  ; cancelled = false
  }

let wakeup t =
  let first =
    Mutex.protect t.mutex @@ fun () ->
    if t.cancelled then (
      false
    ) else (
      t.cancelled <- true;
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
  if first then Condition.notify t.condition;
  first

let prepare_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  t.cancelled <- false

type status = Wakeup_received | No_wakeup
let cancel_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  if t.cancelled then (
    (* We received a notification between [prepare] and [cancel]. *)
    Wakeup_received
  ) else (
    (* Update [last_wakeup] so that a future wakeup
       on this round is not counted as 'useful'. *)
    t.cancelled <- true;
    No_wakeup
  )

let commit_sleep t =
  Mutex.protect t.mutex @@ fun () ->
  if t.cancelled then (
    (* we received a notification between [prepare] and [commit] *)
    ()
  ) else (
    Condition.wait t.condition t.mutex;
    t.cancelled <- true
  )
