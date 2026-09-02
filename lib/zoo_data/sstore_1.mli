type t

type 'a ref

val create :
  unit -> t

val ref :
  t -> 'a -> 'a ref
val get :
  t -> 'a ref -> 'a
val set :
  t -> 'a ref -> 'a -> unit

type snapshot

val capture :
  t -> snapshot
val restore :
  t -> snapshot -> unit
