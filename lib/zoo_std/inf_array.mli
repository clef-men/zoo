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

val cas :
  'a t -> int -> 'a -> 'a -> bool

val faa :
  int t -> int -> int -> int
