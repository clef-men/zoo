type ('context, 'a) t

type ('context, 'a) waiter =
  'context -> 'a -> unit

val create :
  unit -> ('context, 'a) t

val make :
  'a -> ('context, 'a) t

val is_unset :
  ('context, 'a) t -> bool
val is_set :
  ('context, 'a) t -> bool

val try_get :
  ('context, 'a) t -> 'a option

val get :
  ('context, 'a) t -> 'a

val wait :
  ('context, 'a) t -> ('context, 'a) waiter -> 'a option

val set :
  ('context, 'a) t -> 'a -> ('context, 'a) waiter list

val notify :
  ('context, 'a) t -> 'context -> 'a -> unit
