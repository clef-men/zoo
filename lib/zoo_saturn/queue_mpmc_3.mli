type 'a t

val create :
  unit -> 'a t

val size :
  'a t -> int

val is_empty :
  'a t -> bool

val push_back :
  'a t -> 'a -> unit

val push_front :
  'a t -> 'a -> unit

val pop :
  'a t -> 'a option
