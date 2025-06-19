type 'a t

val create :
  'a -> 'a t

val get :
  'a t -> int -> 'a

val update :
  'a t -> int -> ('a -> 'a) -> 'a

val set :
  'a t -> int -> 'a -> unit

val xchg :
  'a t -> int -> 'a -> 'a
val xchg_resolve :
  'a t -> int -> 'a -> 'b Zoo.proph' -> 'b -> 'a

val cas :
  'a t -> int -> 'a -> 'a -> bool
val cas_resolve :
  'a t -> int -> 'a -> 'a -> 'b Zoo.proph' -> 'b -> bool

val faa :
  int t -> int -> int -> int
