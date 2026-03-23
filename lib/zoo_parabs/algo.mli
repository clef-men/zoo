val for_ :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> int -> unit) Pool.task ->
  unit
(** Suppose that [task : (int -> int -> unit) Pool.task] performs a
    potentially asynchronous computation on an interval of indices:
    [task ctx beg end_] computes a certain result on all indices from
    [beg] (included) to [end_] (excluded).

    Then, [for_ ctx beg end_ chunk task] will call [task] on a partition
    of sub-intervals between [beg] (included) and [end_] (excluded),
    asynchronously (possibly in any order and in parallel).

    If [chunk] is [Some recommended_size], then the input intervals
    given to [task] will be no larger than [recommended_size], and
    [for_] will try to choose intervals whose size is close to the
    [recommended_size]. Otherwise a default chunk size will be chosen
    to create a small number of tasks per worker domain.

    For example, to double the elements of an array [t], you could run
    {[
    let double ctx t =
      let task ctx beg end_ =
        for i = beg to end_ - 1 do
          t.(i) <- t.(i) * 2
        done
      in Algo.for_ ctx 0 (Array.length t) None task
    ]}
 *)

val for_each :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> unit) Pool.task ->
  unit
(** [for_each ctx beg end_ chunk task] will call [task] asynchronously
    on each index between [beg] (included) and [end_] (excluded), possibly
    in any order and in parallel.

    If [chunk] is [Some recommended_size], then [for_each] will call
    [task] sequentially on sub-intervals of size below
    [recommended_size]. Otherwise a default chunk size will be chosen
    to create a small number of tasks per worker domain.

    For example, to double the elements of an array [t], you could run
    {[
    let double ctx t =
      let task ctx i =
        t.(i) <- t.(i) * 2
      in Algo.for_each ctx 0 (Array.length t) None task
    ]}

 **)

val fold :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> 'a) Pool.task ->
  ('a -> 'a -> 'a) ->
  'a ->
  'a
(** [fold ctx beg end_ chunk task op zero] will run [task] on each
    index between [beg] (included) and [end_] (excluded), possibly in any
    order and in parallel, merging results with [op] and using [zero]
    on empty sub-intervals.

    If [chunk] is [Some recommended_size], then [fold] will call [task]
    sequentially on sub-intervals of size below [recommended_size].

    For example, to sum the elements of an array [t], you could run
    {[
    let sum ctx t =
      Algo.fold ctx 0 (Array.length t) (fun i -> t.(i)) (+) 0
    ]}
 *)

val find :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> bool) Pool.task ->
  int option
(** [find ctx beg end_ chunk pred] returns [true]
    if [pred ctx i] is true for any of the indices
    between [beg] (included) and [end_] (excluded).

   If [chunk] is [Some recommended_size], then [fold] will call [pred]
   sequentially on sub-intervals of size below [recommended_size].

    For example, to check if the array [t] contains a [0], you could run
    {[
    let has_zero ctx t =
      Algo.find ctx 0 (Array.length t) None (fun i -> t.(i) = 0)
    ]}
 *)
