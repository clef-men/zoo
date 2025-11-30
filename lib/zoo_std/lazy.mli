type 'a t

val make :
  (unit -> 'a) -> 'a t

val return :
  'a -> 'a t

val is_set :
  'a t -> bool
val is_unset :
  'a t -> bool

val get :
  'a t -> 'a
