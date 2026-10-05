type 'a t

val create :
  unit -> 'a t

val send :
  'a t -> 'a -> bool

val recv :
  'a t -> 'a option
