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

val click :
  t -> unit
val observe :
  t -> 'a ref -> 'a
