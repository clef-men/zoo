type 'a t

type 'a elt

val elt_equal :
  'a elt -> 'a elt -> bool
val elt_equiv :
  'a elt -> 'a elt -> bool
val elt_repr :
  'a elt -> 'a elt
val elt_get :
  'a elt -> 'a
val elt_cardinal :
  'a elt -> int

val create :
  'a -> 'a t * 'a elt

val add_same_class :
  'a elt -> 'a -> 'a elt

val add_new_class :
  'a t -> 'a -> 'a elt

val refine :
  'a t -> 'a elt list -> unit
