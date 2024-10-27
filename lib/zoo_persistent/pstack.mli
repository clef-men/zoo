type 'a t

val empty :
  'a t

val is_empty :
  'a t -> bool

val push :
  'a t -> 'a -> 'a t

val pop :
  'a t -> ('a * 'a t) option
