type t
(** A scheduler has a queue of tasks to run, and owns a pool of [n]
    worker domains to run them. One domain owns the scheduler and
    sends a toplevel task using the {!run} function, so in total [n+1]
    domains participate to the computation. *)

type context
(** A [context] carries the execution state of a running scheduler. *)

type 'a task =
  context -> 'a

val create :
  int -> t
(** [create n] creates a new scheduler with [n] extra worker domains. *)

val run :
  t -> 'a task -> 'a
(** [run t task] runs a toplevel task on a given scheduler; subtasks
    will run on this (caller) domain or on the worker domains. It
    returns when the toplevel task is finished. *)

val kill :
  t -> unit
(** [kill t] stops a scheduler: it terminates the worker domains when
    they run out of tasks, and returns when all workers are done. It
    should be called once you know that the topevel task you care
    about is finished. *)

val size :
  context -> int
(** [size ctx] returns the number of worker domains of the scheduler
    of this context. This can be useful for coarse-grained splitting
    of sequences of inputs, to schedule one task per domain. *)

val async :
  context -> unit task -> unit
(** [async ctx task] schedules the [task] to be executed asynchronously
    by the scheduler. *)

val wait_until :
  context -> (unit -> bool) -> unit
(** [wait_until ctx pred] waits until [pred ()] returns [true],
    working on other tasks in the meantime. *)

val wait_while :
  context -> (unit -> bool) -> unit
(** [wait_while ctx pred] is [wait_until ctx (fun () -> not (pred ()))]. *)
