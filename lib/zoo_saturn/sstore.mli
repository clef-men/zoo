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
val xchg :
  t -> 'a ref -> 'a -> 'a
val cas :
  t -> 'a ref -> 'a -> 'a -> bool

val click :
  t -> unit
val observe :
  t -> 'a ref -> 'a
