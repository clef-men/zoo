type 'a t

val create :
  int -> 'a t

val capacity :
  'a t -> int

val size :
  'a t -> int

val is_empty :
  'a t -> bool

val push :
  'a t -> 'a -> bool

val pop :
  'a t -> 'a option
