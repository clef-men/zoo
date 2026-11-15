type ('k, 'v) t

val create :
  hash:('k -> int) -> equal:('k -> 'k -> bool) -> ('k, 'v) t

val size :
  ('k, 'v) t -> int

val mem :
  ('k, 'v) t -> 'k -> bool

val find :
  ('k, 'v) t -> 'k -> 'v option

val add :
  ('k, 'v) t -> 'k -> 'v -> bool

val find_and_remove :
  ('k, 'v) t -> 'k -> 'v option

val remove :
  ('k, 'v) t -> 'k -> unit

val find_and_replace :
  ('k, 'v) t -> 'k -> 'v -> 'v option

val replace :
  ('k, 'v) t -> 'k -> 'v -> unit
