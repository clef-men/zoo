type 'a t =
  'a list

val singleton :
  'a -> 'a t

val head :
  'a t -> 'a
val tail :
  'a t -> 'a t

val is_empty :
  'a t -> bool

val get :
  'a t -> int -> 'a

val initi :
  int -> (int -> 'a) -> 'a t
val init :
  int -> (unit -> 'a) -> 'a t

val foldli :
  'a t -> 'b -> ('b -> int -> 'a -> 'b) -> 'b
val foldl :
  'a t -> 'b -> ('b -> 'a -> 'b) -> 'b

val foldri :
  'a t -> (int -> 'a -> 'b -> 'b) -> 'b -> 'b
val foldr :
  'a t -> ('a -> 'b -> 'b) -> 'b -> 'b

val size :
  'a t -> int

val rev_app :
  'a t -> 'a t -> 'a t
val rev :
  'a t -> 'a t

val app :
  'a t -> 'a t -> 'a t
val snoc :
  'a t -> 'a -> 'a t

val iteri :
  'a t -> (int -> 'a -> unit) -> unit
val iter :
  'a t -> ('a -> unit) -> unit

val mapi :
  'a t -> (int -> 'a -> 'b) -> 'b t
val map :
  'a t -> ('a -> 'b) -> 'b t
