(** The [Pool] module exposes a low-level interface of a pool of
    worker domains on which asynchronous tasks can be scheduled.

    You need to use {!create} and {!run_on} to start asynchronous
    computations, and {!close} to release the worker domains at the
    end.

    The other functions of the module are basic building blocks on
    which higher-level APIs can be built. For parallel processing of
    arrays, we recommend using the higher-level {!Algo} module. For
    general asynchronous computations we recommend the {!Future}
    module.

    For example, here is a complete program computing [fibonacci 40],
    using the [fibo] example from the {!Future} module:
    {[
    let () =
      let pool = Pool.create ~num_worker:(Domain.recommended_domain_count () - 1) in
      let fib40 = Pool.run_on pool (fun ctx -> fibo ctx 40) in
      Pool.close pool;
      fib40
    ]}
 *)

type t
(** A pool of [n] worker domains. One domain owns the pool and sends
    toplevels tasks using the {!run_on} function, so in total [n+1]
    domains participate to the computation. *)

type context
(** A [context] carries the execution state of a running pool. *)

type 'a task =
  context -> 'a

val create :
  num_worker:int -> t
(** [create ~num_worker] creates a new pool with [num_worker] extra worker domains. *)

val run_on :
  t -> 'a task -> 'a
(** [run_on t task] runs [task] on pool [t]; subtasks will run on this
    (caller) domain or on the worker domains. It returns when [task] is
    finished. *)

val close :
  t -> unit
(** [close t] stops pool [t]: it terminates the worker domains when
    they run out of tasks, and returns when all workers are done. It
    should be called once you know that the topevel task you care
    about is finished. *)

val run :
  num_worker:int -> 'a task -> 'a
(** [run task] creates a pool with [num_worker] extra worker domains,
    runs [task] on it and closes the pool. *)

val size :
  context -> int
(** [size ctx] returns the number of worker domains of the pool
    of this context. This can be useful for coarse-grained splitting
    of sequences of inputs, to schedule one task per domain. *)

val async :
  context -> unit task -> unit
(** [async ctx task] schedules the [task] to be executed asynchronously
    by the pool. *)

val wait :
  context ->
  notification:((unit -> unit) -> unit) ->
  pred:(unit -> bool) ->
  unit
(** [wait ctx ~notification ~pred] waits until [pred ()] returns [true],
    working on other tasks in the meantime. If the worker is put
    to sleep because no other task is available, [notification] will
    be called with a wakeup callback.

    We assume that [pred ()] is a cheap and monotonic function:
    once it returns [true], it will return [true] forever.

    We assume that [notification] will eventually call the wakeup
    callback if/when [pred ()] changes from [false] to [true]. In
    particular, [notification] is allowed to drop the callback if it
    observes that [pred ()] already holds. *)

val wait_ivar :
  context -> ('a, ('a -> unit) task) Ivar_3.t -> unit
(** [wait_ivar ctx ivar] waits until [ivar] is set,
    working on other tasks in the meantime.  *)
