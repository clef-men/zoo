type 'a t

val create :
  unit -> 'a t

val push :
  'a t -> 'a -> unit

val pop :
  'a t -> 'a option

val steal :
  'a t -> 'a option
