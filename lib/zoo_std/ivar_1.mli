type 'a t

val create :
  unit -> 'a t

val make :
  'a -> 'a t

val is_set :
  'a t -> bool

val try_get :
  'a t -> 'a option

val get :
  'a t -> 'a

val set :
  'a t -> 'a -> unit
