type 'a t

val create :
  unit -> 'a t

val push :
  'a t -> 'a -> bool

val pop :
  'a t -> 'a Optional.t

val is_closed :
  'a t -> bool

val close :
  'a t -> unit
