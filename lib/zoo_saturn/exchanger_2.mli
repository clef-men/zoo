type 'a t

val create :
  cap_log:int -> 'a t

val exchange :
  'a t -> 'a -> 'a option
