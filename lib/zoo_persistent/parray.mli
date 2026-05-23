type 'a t

val make :
  ('a -> 'a -> bool) -> int -> 'a -> 'a t

val get :
  'a t -> int -> 'a
val set :
  'a t -> int -> 'a -> 'a t
