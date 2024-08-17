type 'a t

val create :
  int -> 'a t

val push :
  'a t -> 'a -> unit

val pop :
  'a t -> 'a
