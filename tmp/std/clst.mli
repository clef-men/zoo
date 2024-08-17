type 'a t =
  | ClstClosed
  | ClstOpen
  | ClstCons of 'a * 'a t

val app :
  'a t -> 'a t -> 'a t

val rev_app :
  'a t -> 'a t -> 'a t

val iter :
  'a t -> ('a -> unit) -> unit
