type 'a t =
  | Gnil
  | Gcons of 'a * 'a t [@generative]

val rev_app :
  'a t -> 'a t -> 'a t

val rev :
  'a t -> 'a t
