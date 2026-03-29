(** The [Future] module exposes a high-level interface for
    asynchronous computations that depend on each others' results.

    For example, here would be a realistic parallel version
    of the naive recursive definition of the [fibonacci]
    function.
    {[
    let rec fibo_seq n =
      if n <= 1 then n
      else fibo_seq (n - 1) + fibo_seq (n - 2)

    let sequential_cutoff = 20

    let rec fibo ctx n =
      if n <= sequential_cutoff then fibo_seq n
      else
        let a = Future.async ctx (fun ctx -> fibo ctx (n - 1)) in
        let b = fibo ctx (n - 2) in
        Future.wait a + b
    ]}
 *)

type 'a t
(** A future of type ['a t] represents the future result of type ['a]
    of some asynchronous task. *)

val return :
  'a -> 'a t

val async :
  Pool.context -> 'a Pool.task -> 'a t
(** [async ctx task] schedules [task] to run asynchronously on the
    scheduler [ctx], and returns a future for its result. *)

val wait :
  Pool.context -> 'a t -> 'a
(** [wait ctx future] blocks until the [future] result
    is available and returns it; the caller domain helps
    running scheduled tasks in the meantime. *)

val iter :
  Pool.context -> 'a t -> ('a -> unit) Pool.task -> unit
(** [iter ctx fut task] schedules the [unit]-returning [task] to run on
    the result of the future [fut] when available, and returns
    immediately. *)

val map :
  Pool.context -> 'a t -> ('a -> 'b) Pool.task -> 'b t
(** [map ctx fut task] schedules [task] to run once the
    result of the future [fut] is available, and returns
    a future for its result. *)
