type ('a, 'b) proph
type 'a proph' =
  (unit, 'a) proph

val proph :
  unit -> ('a, 'b) proph
val resolve_with :
  'a -> ('a, 'b) proph -> 'b -> 'a
val resolve_silent :
  'a proph' -> 'a -> unit
val resolve :
  'a proph' -> 'a -> 'a

type id

val id :
  unit -> id
