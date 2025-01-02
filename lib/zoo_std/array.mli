type 'a t =
  'a array

val unsafe_alloc :
  int -> 'a t
val alloc :
  int -> 'a t

val create :
  unit -> 'a t

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

val unsafe_fill_slice :
  'a t -> int -> int -> 'a -> unit
val fill_slice :
  'a t -> int -> int -> 'a -> unit
val fill :
  'a t -> 'a -> unit

val unsafe_make :
  int -> 'a -> 'a t
val make :
  int -> 'a -> 'a t

val foldli :
  (int -> 'b -> 'a -> 'b) -> 'b -> 'a t -> 'b
val foldl :
  ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

val sum :
  int t -> int

val foldri :
  (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val foldr :
  ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val iteri :
  (int -> 'a -> unit) -> 'a t -> unit
val iter :
  ('a -> unit) -> 'a t -> unit

val applyi :
  (int -> 'a -> 'a) -> 'a t -> unit
val apply :
  ('a -> 'a) -> 'a t -> unit

val unsafe_initi :
  int -> (int -> 'a) -> 'a t
val initi :
  int -> (int -> 'a) -> 'a t
val unsafe_init :
  int -> (unit -> 'a) -> 'a t
val init :
  int -> (unit -> 'a) -> 'a t

val mapi :
  (int -> 'a -> 'b) -> 'a t -> 'b t
val map :
  ('a -> 'b) -> 'a t -> 'b t

val unsafe_copy_slice :
  'a t -> int -> 'a t -> int -> int -> unit
val copy_slice :
  'a t -> int -> 'a t -> int -> int -> unit
val unsafe_copy :
  'a t -> 'a t -> int -> unit
val copy :
  'a t -> 'a t -> int -> unit

val unsafe_grow :
  'a t -> int -> 'a -> 'a t
val grow :
  'a t -> int -> 'a -> 'a t

val unsafe_sub :
  'a t -> int -> int -> 'a t
val sub :
  'a t -> int -> int -> 'a t

val unsafe_shrink :
  'a t -> int -> 'a t
val shrink :
  'a t -> int -> 'a t

val clone :
  'a t -> 'a t

val unsafe_resize_slice :
  'a t -> int -> int -> int -> 'a -> 'a t

val unsafe_cget :
  'a t -> int -> 'a
val cget :
  'a t -> int -> 'a

val unsafe_cset :
  'a t -> int -> 'a -> unit
val cset :
  'a t -> int -> 'a -> unit

val unsafe_ccopy_slice :
  'a t -> int -> 'a t -> int -> int -> unit
val ccopy_slice :
  'a t -> int -> 'a t -> int -> int -> unit
val unsafe_ccopy :
  'a t -> int -> 'a t -> int -> unit
val ccopy :
  'a t -> int -> 'a t -> int -> unit

val unsafe_cresize_slice :
  'a t -> int -> int -> int -> 'a -> 'a t
