type 'a t

val create :
  unit -> 'a t

val set :
  'a t -> 'a -> unit

val try_get :
  'a t -> 'a option
val get :
  'a t -> 'a

val is_set :
  'a t -> bool
