type 'a t

val create :
  unit -> 'a t

val size :
  'a t -> int

val is_empty :
  'a t -> bool

val unsafe_get :
  'a t -> int -> 'a
val unsafe_set :
  'a t -> int -> 'a -> unit

val push :
  'a t -> 'a -> unit

val pop_front :
  'a t -> 'a option
val pop_back :
  'a t -> 'a option
