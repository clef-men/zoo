type 'a t

val make :
  'a -> 'a t

val get :
  'a t -> 'a
val set :
  'a t -> 'a -> unit

val click :
  'a t -> unit
val observe :
  'a t -> 'a
