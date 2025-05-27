type 'a t

val make :
  ('a -> 'a -> bool) -> int -> 'a -> 'a t

val get :
  'a t -> int -> 'a
val set :
  'a t -> int -> 'a -> unit

type 'a snapshot

val capture :
  'a t -> 'a snapshot
val restore :
  'a t -> 'a snapshot -> unit
