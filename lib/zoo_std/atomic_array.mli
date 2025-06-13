[@@@zoo.ignore]

type 'a t

val make :
  int -> 'a -> 'a t

val init :
  int -> (unit -> 'a) -> 'a t
val initi :
  int -> (int -> 'a) -> 'a t

val size :
  'a t -> int

val unsafe_get :
  'a t -> int -> 'a
val get :
  'a t -> int -> 'a

val unsafe_set :
  'a t -> int -> 'a -> unit
val set :
  'a t -> int -> 'a -> unit

val unsafe_xchg :
  'a t -> int -> 'a -> 'a

val unsafe_cas :
  'a t -> int -> 'a -> 'a -> bool

val unsafe_faa :
  int t -> int -> int -> int

val foldli :
  (int -> 'b -> 'a -> 'b) -> 'b -> 'a t -> 'b
val foldl :
  ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

val sum :
  int t -> int
