type 'a t =
  | ClistClosed
  | ClistOpen
  | ClistCons of 'a * 'a t [@generative]

val app :
  'a t -> 'a t -> 'a t

val rev_app :
  'a t -> 'a t -> 'a t

val iter :
  ('a -> unit) -> 'a t -> unit
