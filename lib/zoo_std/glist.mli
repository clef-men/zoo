type 'a t =
  | Nil
  | Cons of 'a * 'a t [@generative]

val rev_app :
  'a t -> 'a t -> 'a t

val rev :
  'a t -> 'a t
