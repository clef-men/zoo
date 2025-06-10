type ('a, 'waiter) t

val create :
  unit -> ('a, 'waiter) t

val make :
  'a -> ('a, 'waiter) t

val is_set :
  ('a, 'waiter) t -> bool

val try_get :
  ('a, 'waiter) t -> 'a option

val get :
  ('a, 'waiter) t -> 'a

val wait :
  ('a, 'waiter) t -> 'waiter -> 'a option

val set :
  ('a, 'waiter) t -> 'a -> 'waiter list
