type 'a t

val create :
  unit -> 'a t

val exchange :
  'a t -> 'a -> 'a option
