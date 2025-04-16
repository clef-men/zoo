type 'a t

type 'a waiter =
  'a -> unit

val create :
  unit -> 'a t

val is_set :
  'a t -> bool

val try_get :
  'a t -> 'a option

val get :
  'a t -> 'a

val wait :
  'a t -> 'a waiter -> 'a option

val set :
  'a t -> 'a -> 'a waiter list
