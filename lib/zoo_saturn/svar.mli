type 'a t

val make :
  'a -> 'a t

val get :
  'a t -> 'a
val set :
  'a t -> 'a -> unit
val xchg :
  'a t -> 'a -> 'a
val cas :
  'a t -> 'a -> 'a -> bool

val click :
  'a t -> unit
val observe :
  'a t -> 'a
