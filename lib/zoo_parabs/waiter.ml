type t =
  { mutex : Mutex.t
  ; condition : Condition.t
  ; mutable cancelled : bool;
  }
(* [cancelled] is protected by the mutex. *)

let create () =
  { mutex = Mutex.create ()
  ; condition = Condition.create ()
  ; cancelled = false;
  }

type status = First | Already_notified

let notify t =
  let first =
    Mutex.protect t.mutex @@ fun () ->
    if t.cancelled then (
      false
    ) else (
      t.cancelled <- true;
      true
    )
    (* We also take the mutex to synchronize with [commit].

       After taking the mutex we know that either [commit] saw that
       the [cancelled] flag was already set, or it finished its own
       critical section so [Condition.wait] has been called.

       Otherwise we would risk losing the notification by calling
       [Condition.notify] below before [commit] calls
       [Condition.wait].
    *)
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
  if first then (
    Condition.notify t.condition;
    First
  ) else (
    Already_notified 
  )

let prepare t =
  Mutex.protect t.mutex @@ fun () ->
  t.cancelled <- false

let cancel t =
  Mutex.protect t.mutex @@ fun () ->
  if t.cancelled then (
    (* We received a notification between [prepare] and [cancel]. *)
    Already_notified
  ) else (
    (* Update [last_wakeup] so that a future notification is not
       counted as 'useful'. *)
    t.cancelled <- true;
    First
  )

let commit t =
  Mutex.protect t.mutex @@ fun () ->
  if t.cancelled then (
    (* we received a notification between [prepare] and [commit] *)
    ()
  ) else (
    Condition.wait t.condition t.mutex;
    t.cancelled <- true
  )
