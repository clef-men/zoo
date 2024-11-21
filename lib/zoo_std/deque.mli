type 'a t

val create :
  unit -> 'a t

val is_empty :
  'a t -> bool

val push_front :
  'a t -> 'a -> unit
val push_back :
  'a t -> 'a -> unit

val pop_front :
  'a t -> 'a option
val pop_back :
  'a t -> 'a option

val iter :
  ('a -> unit) -> 'a t -> unit
