type 'a t

val create :
  unit -> 'a t

val push_front :
  'a t -> 'a -> bool

val push_back :
  'a t -> 'a -> bool

val pop_front :
  'a t -> 'a option

val close :
  'a t -> bool

val is_empty :
  'a t -> bool
