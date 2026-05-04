type 'a t

val create :
  int -> 'a t

val make :
  int -> 'a -> 'a t

val is_empty :
  'a t -> bool

val push :
  'a t -> 'a -> bool

val pop :
  'a t -> 'a Optional.t
