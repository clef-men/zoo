type 'a elt

val make :
  'a -> 'a elt
val make_same_class :
  'a elt -> 'a -> 'a elt

val get :
  'a elt -> 'a

val equal :
  'a elt -> 'a elt -> bool
val equiv :
  'a elt -> 'a elt -> bool

val repr :
  'a elt -> 'a elt

val cardinal :
  'a elt -> int

val refine :
  'a elt list -> unit
