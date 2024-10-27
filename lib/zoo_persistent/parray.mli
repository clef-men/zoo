type 'a t

val make :
  int -> 'a -> 'a t

val get :
  'a t -> int -> 'a
val set :
  'a t -> ('a -> 'a -> bool) -> int -> 'a -> 'a t
