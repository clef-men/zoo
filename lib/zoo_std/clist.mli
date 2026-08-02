type 'a t =
  | Closed
  | Open
  | Cons of 'a * 'a t [@generative]

val app :
  'a t -> 'a t -> 'a t

val rev_app :
  'a t -> 'a t -> 'a t

val iter :
  ('a -> unit) -> 'a t -> unit
