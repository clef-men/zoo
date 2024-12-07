type 'a t

val create :
  int -> 'a t

val size :
  'a t -> int

val is_empty :
  'a t -> bool

val push :
  'a t -> 'a -> bool

val pop :
  'a t -> 'a option
