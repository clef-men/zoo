type 'a t

val cons :
  'a -> 'a t -> 'a t

val head :
  'a t -> 'a
val tail :
  'a t -> 'a t

val set_head :
  'a t -> 'a -> unit
val set_tail :
  'a t -> 'a t -> unit
