type 'a t

val create :
  'a -> 'a t

val get :
  'a t -> int -> 'a
val set :
  'a t -> int -> 'a -> unit
