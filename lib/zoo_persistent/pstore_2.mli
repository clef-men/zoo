type 'a t

type 'a ref

val create :
  unit -> 'a t

val ref :
  'a t -> 'a -> 'a ref
val get :
  'a t -> 'a ref -> 'a
val set :
  'a t -> 'a ref -> 'a -> unit

type 'a snapshot

val capture :
  'a t -> 'a snapshot
val restore :
  'a t -> 'a snapshot -> unit
