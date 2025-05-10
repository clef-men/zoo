type 'a proph

val proph :
  unit -> 'a proph
val resolve :
  'a -> 'b proph -> 'b -> 'a
val resolve' :
  'a proph -> 'a -> unit

type id

val id :
  unit -> id
