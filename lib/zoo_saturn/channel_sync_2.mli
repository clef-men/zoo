type 'a t

val create :
  cap_log:int -> 'a t

val send :
  'a t -> 'a -> bool

val recv :
  'a t -> 'a option
