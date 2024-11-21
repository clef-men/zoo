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
  (int -> 'b -> 'a -> 'b) -> 'b -> 'a t -> 'b
val foldl :
  ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

val foldri :
  (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val foldr :
  ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

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
  (int -> 'a -> unit) -> 'a t -> unit
val iter :
  ('a -> unit) -> 'a t -> unit

val mapi :
  (int -> 'a -> 'b) -> 'a t -> 'b t
val map :
  ('a -> 'b) -> 'a t -> 'b t
