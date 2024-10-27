type 'a t
type 'a ref
type 'a snap

val create :
  unit -> 'a t

val ref :
  'a t -> 'a -> 'a ref
val get :
  'a t -> 'a ref -> 'a
val set :
  'a t -> 'a ref -> 'a -> unit

val capture :
  'a t -> 'a snap
val restore :
  'a t -> 'a snap -> unit
