type 'a t

val create :
  int -> 'a t

val push :
  'a t -> 'a -> bool

val pop :
  'a t -> 'a option
