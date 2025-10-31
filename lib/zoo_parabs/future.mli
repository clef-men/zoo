type 'a t

val async :
  Pool.context -> 'a Pool.task -> 'a t

val wait :
  Pool.context -> 'a t -> 'a

val iter :
  Pool.context -> 'a t -> ('a -> unit) Pool.task -> unit

val map :
  Pool.context -> 'a t -> ('a -> 'b) Pool.task -> 'b t
