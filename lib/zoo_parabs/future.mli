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
